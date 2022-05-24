module SystematicDiophantineEquations

export Monomial, Polynomial, all_polynomials, irreducible_polynomials,
    dedup, nontrivial_polynomials

using Graphs
using Singular
using StaticArrays

################################################################################

function incr_partition!(x::Vector{Int})
    @inbounds begin
        n = length(x)
        if n <= 1
            return false
        end
        xn = x[n]
        xn1 = x[n - 1]
        if xn1 != 0
            x[n - 1] = xn1 - 1
            x[n] = xn + 1
            return true
        end
        for i = n - 2 : -1 : 1
            xi = x[i]
            if xi != 0
                x[i] = xi - 1
                if xn == 0
                    x[i + 1] += 1
                else
                    x[i + 1] += xn + 1
                    x[n] = 0
                end
                return true
            end
        end
        return false
    end
end

function integer_partitions(n::Int, len::Int)
    result = Vector{Int}[]
    if n == 0 && len == 0
        push!(result, Int[])
    elseif n >= 0 && len >= 1
        p = zeros(Int, len)
        p[1] = n
        while true
            push!(result, copy(p))
            if !incr_partition!(p)
                break
            end
        end
    end
    return result
end

################################################################################

struct HomogeneousPolynomialIterator{N}
    monomials::Vector{NTuple{N, Int}}
    dense_partition::Vector{Int}
    sparse_partition::Vector{Tuple{Int, Int}}
    sign_pattern::Array{UInt, 0}
    function HomogeneousPolynomialIterator{N}(weight::Int,
                                              degree::Int) where {N}
        monomials = NTuple{N, Int}.(integer_partitions(degree, N))
        dense_partition = zeros(Int, length(monomials))
        dense_partition[1] = weight
        sparse_partition = [(weight, 1)]
        sign_pattern = fill(UInt(0))
        return new(monomials, dense_partition, sparse_partition, sign_pattern)
    end
end

const Monomial{N} = Tuple{Int, NTuple{N, Int}}
const Polynomial{N} = Vector{Monomial{N}}
const HPI{N} = HomogeneousPolynomialIterator{N}

function append_polynomial!(poly::Polynomial{N}, it::HPI{N}) where {N}
    s = it.sign_pattern[]
    m = it.monomials
    for (c, i) in it.sparse_partition
        push!(poly, (ifelse(s & 1 == 0, +c, -c), m[i]))
        s >>= 1
    end
    return poly
end

function incr_polynomial!(it::HPI{N}) where {N}
    dense = it.dense_partition
    sparse = it.sparse_partition
    s = it.sign_pattern[] + 1
    if s < (UInt(1) << length(sparse))
        it.sign_pattern[] = s
        return true
    else
        it.sign_pattern[] = UInt(0)
        if !incr_partition!(dense)
            return false
        end
        empty!(sparse)
        for (i, c) in enumerate(dense)
            if c != 0
                push!(sparse, (c, i))
            end
        end
        return true
    end
end

################################################################################

function get_polynomial(iterators::Vector{HPI{N}}) where {N}
    result = Monomial{N}[]
    for it in iterators
        append_polynomial!(result, it)
    end
    return result
end

function reset!(it::HPI{N}) where {N}
    dense = it.dense_partition
    sparse = it.sparse_partition
    weight = sum(dense)
    fill!(dense, 0)
    dense[1] = weight
    empty!(sparse)
    push!(sparse, (weight, 1))
    it.sign_pattern[] = UInt(0)
    return it
end

function incr_polynomial!(iterators::Vector{HPI{N}}) where {N}
    i = length(iterators)
    while true
        if i == 0
            return false
        end
        if incr_polynomial!(iterators[i])
            return true
        end
        reset!(iterators[i])
        i -= 1
    end
end

################################################################################

function ilog2(n::Int)
    return 8 * sizeof(Int) - leading_zeros(n) - 1
end

function power_of_two_partitions(n::Int, k::Int)
    if n == 0
        return [Tuple{Int, Int}[]]
    else
        result = Vector{Tuple{Int, Int}}[]
        for j = k : -1 : 0
            for i = (n >> j) : -1 : 1
                for p in power_of_two_partitions(n - i * (1 << j), j - 1)
                    push!(result, vcat([(i, j)], p))
                end
            end
        end
        return result
    end
end

function power_of_two_partitions(n::Int)
    return power_of_two_partitions(n, ilog2(n))
end

################################################################################

function all_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    for partition in power_of_two_partitions(height)
        iterators = [
            HomogeneousPolynomialIterator{N}(weight, degree)
            for (weight, degree) in partition
        ]
        while true
            push!(result, get_polynomial(iterators))
            if !incr_polynomial!(iterators)
                break
            end
        end
    end
    return result
end

################################################################################

function uses_variable(p::Polynomial{N}, i::Int) where {N}
    @inbounds for (c, m) in p
        if m[i] != 0
            return true
        end
    end
    return false
end

function uses_all_variables(p::Polynomial{N}) where {N}
    for i = 1 : N
        if !uses_variable(p, i)
            return false
        end
    end
    return true
end

function has_coprime_coefficients(p::Polynomial{N}) where {N}
    result = 0
    for (c, m) in p
        result = gcd(result, c)
        if result == 1
            return true
        end
    end
    return false
end

function irreducible_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    for partition in power_of_two_partitions(height)
        iterators = [
            HomogeneousPolynomialIterator{N}(weight, degree)
            for (weight, degree) in partition
        ]
        while true
            p = get_polynomial(iterators)
            if uses_all_variables(p) && has_coprime_coefficients(p)
                push!(result, p)
            end
            if !incr_polynomial!(iterators)
                break
            end
        end
    end
    return result
end

################################################################################

apply_transposition(m::Monomial{1}) = m

function apply_transposition((c, (i, j, k...))::Monomial{N}) where {N}
    return (c, (j, i, k...))
end

function apply_transposition!(p::Polynomial{N}) where {N}
    @inbounds for i = 1 : length(p)
        p[i] = apply_transposition(p[i])
    end
    return p
end

function apply_cycle((c, (i, j...))::Monomial{N}) where {N}
    return (c, (j..., i))
end

function apply_cycle!(p::Polynomial{N}) where {N}
    @inbounds for i = 1 : length(p)
        p[i] = apply_cycle(p[i])
    end
    return p
end

function apply_negation((c, m)::Monomial{N}) where {N}
    return (-c, m)
end

function apply_negation!(p::Polynomial{N}) where {N}
    @inbounds for i = 1 : length(p)
        p[i] = apply_negation(p[i])
    end
    return p
end

function apply_signflip((c, (i, j...))::Monomial{N}) where {N}
    return (ifelse(i & 1 == 0, c, -c), (i, j...))
end

function apply_signflip!(p::Polynomial{N}) where {N}
    @inbounds for i = 1 : length(p)
        p[i] = apply_signflip(p[i])
    end
    return p
end

@inline function ((c, p)::Monomial{N})(x::NTuple{N, T}) where {N, T}
    @inbounds return c * prod(ntuple(i -> x[i]^p[i], Val{N}()))
end

@inline function (p::Polynomial{N})(x::NTuple{N, T}) where {N, T}
    result = 0
    @inbounds for m in p
        result += m(x)
    end
    return result
end

function dedup(polys::Vector{Polynomial{N}}) where {N}
    index_dict = Dict{Polynomial{N}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    g = SimpleGraph(index_dict.count)
    for (i, p_original) in enumerate(polys)
        p = copy(p_original)
        add_edge!(g, i, index_dict[sort!(apply_transposition!(p))])
        apply_transposition!(p)
        add_edge!(g, i, index_dict[sort!(apply_negation!(p))])
        apply_negation!(p)
        add_edge!(g, i, index_dict[sort!(apply_signflip!(p))])
        apply_signflip!(p)
        add_edge!(g, i, index_dict[sort!(apply_cycle!(p))])
    end
    _, vars = PolynomialRing(ZZ, ["" for _ = 1 : N])
    x = ntuple(i -> (@inbounds vars[i]), Val{N}())
    result = Polynomial{N}[]
    for comp in connected_components(g)
        @inbounds p = polys[comp[1]]
        if length(factor(p(x)).fac) == 1
            push!(result, p)
        end
    end
    return result
end

################################################################################

function is_positive_semidefinite(p::Polynomial{N}) where {N}
    for (c, m) in p
        if c < 0 || !all(m .& 1 .== 0)
            return false
        end
    end
    return true
end

function is_negative_semidefinite(p::Polynomial{N}) where {N}
    for (c, m) in p
        if c > 0 || !all(m .& 1 .== 0)
            return false
        end
    end
    return true
end

function has_linear_variable(p::Polynomial{N}, i::Int) where {N}
    @inbounds (_, n) = p[i]
    @inbounds for (j, (_, m)) in enumerate(p)
        if i != j && !all(iszero.(min.(m, n)))
            return false
        end
    end
    return true
end

function has_linear_variable(p::Polynomial{N}) where {N}
    @inbounds for (i, (_, m)) in enumerate(p)
        if any(m .== 1) && has_linear_variable(p, i)
            return true
        end
    end
    return false
end

function shell(::Val{N}, n::Int) where {N}
    result = NTuple{N, Int}[]
    for x in Iterators.product(ntuple(_ -> -n:n, Val{N}())...)
        if maximum(abs.(x)) == n
            push!(result, x)
        end
    end
    return result
end

function positive_orthant(::Val{N}, n::Int) where {N}
    result = NTuple{N, Int}[]
    for x in Iterators.product(ntuple(_ -> 0:n-1, Val{N}())...)
        push!(result, x)
    end
    return result
end

function has_root(p::Polynomial{N},
                  trial_roots::Vector{NTuple{N, Int}}) where {N}
    for x in trial_roots
        if p(x) == 0
            return true
        end
    end
    return false
end

function has_root_modulo(p::Polynomial{N}, k::Int,
                         trial_roots::Vector{NTuple{N, Int}}) where {N}
    for x in trial_roots
        if p(x) % k == 0
            return true
        end
    end
    return false
end

function nontrivial_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    trial_roots = reduce(vcat, shell(Val{N}(), k) for k = 0 : 3)
    trial_roots_2 = positive_orthant(Val{N}(), 2)
    trial_roots_3 = positive_orthant(Val{N}(), 3)
    trial_roots_4 = positive_orthant(Val{N}(), 4)
    trial_roots_5 = positive_orthant(Val{N}(), 5)
    for partition in power_of_two_partitions(height)
        iterators = [
            HomogeneousPolynomialIterator{N}(weight, degree)
            for (weight, degree) in partition
        ]
        while true
            p = get_polynomial(iterators)
            if (uses_all_variables(p) &&
                !has_linear_variable(p) &&
                !is_positive_semidefinite(p) &&
                !is_negative_semidefinite(p) &&
                has_coprime_coefficients(p) &&
                has_root_modulo(p, 2, trial_roots_2) &&
                has_root_modulo(p, 3, trial_roots_3) &&
                has_root_modulo(p, 4, trial_roots_4) &&
                has_root_modulo(p, 5, trial_roots_5) &&
                !has_root(p, trial_roots))
                push!(result, p)
            end
            if !incr_polynomial!(iterators)
                break
            end
        end
    end
    return result
end

################################################################################

end # module SystematicDiophantineEquations
