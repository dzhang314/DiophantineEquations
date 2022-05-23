module SystematicDiophantineEquations

export Monomial, Polynomial,
    all_polynomials, reduced_polynomials, unique_polynomials,
    nontrivial_polynomials, unique_nontrivial_polynomials

using Graphs
using Singular
using StaticArrays

################################################################################

function integer_partitions_impl!(result::Vector{Vector{Int}}, n::Int,
                                  partition::Vector{Int}, len::Int)
    if len == 0
        if n == 0
            push!(result, copy(partition))
        end
    elseif len == 1
        push!(partition, n)
        push!(result, copy(partition))
        Base._deleteend!(partition, 1)
    elseif len > 1
        for k = n : -1 : 0
            push!(partition, k)
            integer_partitions_impl!(result, n - k, partition, len - 1)
            Base._deleteend!(partition, 1)
        end
    end
    return result
end

function integer_partitions(n::Int, len::Int)
    return integer_partitions_impl!(Vector{Int}[], n, Int[], len)
end

################################################################################

function signed_partitions_impl!(result::Vector{Vector{Int}}, n::Int,
                                 partition::Vector{Int}, len::Int)
    if len == 0
        if n == 0
            push!(result, copy(partition))
        end
    elseif len == 1
        if n == 0
            push!(partition, 0)
            push!(result, copy(partition))
            Base._deleteend!(partition, 1)
        else
            push!(partition, +n)
            push!(result, copy(partition))
            Base._deleteend!(partition, 1)
            push!(partition, -n)
            push!(result, copy(partition))
            Base._deleteend!(partition, 1)
        end
    elseif len > 1
        for k = n : -1 : 1
            push!(partition, +k)
            signed_partitions_impl!(result, n - k, partition, len - 1)
            Base._deleteend!(partition, 1)
            push!(partition, -k)
            signed_partitions_impl!(result, n - k, partition, len - 1)
            Base._deleteend!(partition, 1)
        end
        if n >= 0
            push!(partition, 0)
            signed_partitions_impl!(result, n, partition, len - 1)
            Base._deleteend!(partition, 1)
        end
    end
    return result
end

function signed_partitions(n::Int, len::Int)
    return signed_partitions_impl!(Vector{Int}[], n, Int[], len)
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

const Monomial{N} = Tuple{Int, NTuple{N, Int}}
const Polynomial{N} = Vector{Monomial{N}}

function homogeneous_polynomials(::Val{N}, weight::Int, degree::Int) where {N}
    result = Polynomial{N}[]
    monoms = integer_partitions(degree, N)
    coeffs = signed_partitions(weight, length(monoms))
    for cvec in coeffs
        poly = Monomial{N}[]
        for (c, m) in zip(cvec, monoms)
            if c != 0
                mono = ntuple(i -> Core.arrayref(false, m, i), Val{N}())
                push!(poly, (c, mono))
            end
        end
        push!(result, poly)
    end
    return result
end

function homogeneous_polynomial_table(::Val{N}, height::Int) where {N}
    result = Dict{Tuple{Int, Int}, Vector{Polynomial{N}}}()
    partitions = power_of_two_partitions(height)
    for partition in partitions
        for (i, j) in partition
            if !haskey(result, (i, j))
                result[(i, j)] = homogeneous_polynomials(Val{N}(), i, j)
            end
        end
    end
    return (partitions, result)
end

################################################################################

function all_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    partitions, homogs = homogeneous_polynomial_table(Val{N}(), height)
    for partition in partitions
        product_space = Iterators.product(
            [homogs[(i, j)] for (i, j) in partition]...
        )
        for point in product_space
            push!(result, reduce(vcat, point))
        end
    end
    return result
end

################################################################################

function coefficient_gcd(p::Polynomial{N}) where {N}
    result = 0
    for (c, m) in p
        result = gcd(result, c)
    end
    return result
end

function uses_all_variables(p::Polynomial{N}) where {N}
    return !any(iszero.(sum(SVector{N, Int}(m) for (c, m) in p)))
end

function reduced_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    partitions, homogs = homogeneous_polynomial_table(Val{N}(), height)
    for partition in partitions
        product_space = Iterators.product(
            [homogs[(i, j)] for (i, j) in partition]...
        )
        for point in product_space
            poly = reduce(vcat, point)
            if uses_all_variables(poly) && coefficient_gcd(poly) == 1
                push!(result, poly)
            end
        end
    end
    return result
end

################################################################################

function apply_transposition(m::Monomial{N}) where {N}
    (c, p) = m
    (i, j, k...) = p
    return (c, (j, i, k...))
end

function apply_transposition(p::Polynomial{N}) where {N}
    return apply_transposition.(p)
end

function apply_cycle(m::Monomial{N}) where {N}
    (c, p) = m
    (i, j...) = p
    return (c, (j..., i))
end

function apply_cycle(p::Polynomial{N}) where {N}
    return apply_cycle.(p)
end

function apply_minus(m::Monomial{N}) where {N}
    (c, p) = m
    return (-c, p)
end

function apply_minus(p::Polynomial{N}) where {N}
    return apply_minus.(p)
end

function apply_negation(m::Monomial{N}) where {N}
    (c, p) = m
    return (ifelse(p[1] & 1 != 0, -c, c), p)
end

function apply_negation(p::Polynomial{N}) where {N}
    return apply_negation.(p)
end

function (m::Monomial{N})(x::NTuple{N, T}) where {N, T}
    (c, p) = m
    return c * prod(ntuple(i -> x[i]^p[i], Val{N}()))
end

function (p::Polynomial{N})(x::NTuple{N, T}) where {N, T}
    return sum(m(x) for m in p)
end

function unique_polynomials(::Val{N}, height::Int) where {N}
    polys = reduced_polynomials(Val{N}(), height)
    index_dict = Dict{Polynomial{N}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    g = SimpleGraph(length(polys))
    for (i, p) in enumerate(polys)
        add_edge!(g, i, index_dict[sort!(apply_transposition(p))])
        add_edge!(g, i, index_dict[sort!(apply_negation(p))])
        add_edge!(g, i, index_dict[sort!(apply_cycle(p))])
        add_edge!(g, i, index_dict[sort!(apply_minus(p))])
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

function has_trivial_root(p::Polynomial{N}) where {N}
    for x in Iterators.product(ntuple(_ -> -1:1, Val{N}())...)
        if p(x) == 0
            return true
        end
    end
    return false
end

function has_trivial_variable(p::Polynomial{N}, i::Int) where {N}
    @inbounds for (_, m) in p
        if m[i] != 0
            if m[i] != 1
                return false
            end
            for j = 1 : N
                if i != j && m[j] != 0
                    return false
                end
            end
        end
    end
    return true
end

function has_trivial_variable(p::Polynomial{N}) where {N}
    for i = 1 : N
        if has_trivial_variable(p, i)
            return true
        end
    end
    return false
end

function nontrivial_polynomials(::Val{N}, height::Int) where {N}
    result = Polynomial{N}[]
    for partition in power_of_two_partitions(height)
        if partition[end][2] == 0
            product_space = Iterators.product([
                homogeneous_polynomials(Val{N}(), i, j)
                for (i, j) in partition
            ]...)
            for point in product_space
                poly = reduce(vcat, point)
                if (uses_all_variables(poly) && coefficient_gcd(poly) == 1
                                             && !has_trivial_variable(poly)
                                             && !has_trivial_root(poly))
                    push!(result, poly)
                end
            end
        end
    end
    return result
end

function unique_nontrivial_polynomials(::Val{N}, height::Int) where {N}
    polys = nontrivial_polynomials(Val{N}(), height)
    index_dict = Dict{Polynomial{N}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    g = SimpleGraph(length(polys))
    for (i, p) in enumerate(polys)
        add_edge!(g, i, index_dict[sort!(apply_transposition(p))])
        add_edge!(g, i, index_dict[sort!(apply_negation(p))])
        add_edge!(g, i, index_dict[sort!(apply_cycle(p))])
        add_edge!(g, i, index_dict[sort!(apply_minus(p))])
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

end # module SystematicDiophantineEquations
