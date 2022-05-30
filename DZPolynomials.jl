module DZPolynomials

export Monomial, Polynomial, find_root, has_root_modulo,
    uses_variable, uses_all_variables,
    is_positive_semidefinite, is_negative_semidefinite, to_string, to_latex,
    apply_transposition, apply_cycle, apply_negation, apply_signflip,
    apply_transposition!, apply_cycle!, apply_negation!, apply_signflip!,
    incr_partition!, integer_partitions, binary_partitions,
    HomogeneousPolynomialIterator, get_polynomial, incr_polynomial!,
    l1_ball

################################################################################

const Monomial{T, N, I} = Pair{NTuple{N, I}, T}

const Polynomial{T, N, I} = Vector{Monomial{T, N, I}}

function (p::Polynomial{T, N, I})(x::NTuple{N, X}) where {T, N, I, X}
    result = zero(X)
    for (m, c) in p
        result += *(X(c), Base.power_by_squaring.(x, m)...)
    end
    return result
end

function (p::Polynomial{T, N, I})(x::Vararg{X, N}) where {T, N, I, X}
    return p(x)
end

function find_root(p::Polynomial{T, N, I},
                   xs::Vector{NTuple{N, X}}) where {T, N, I, X}
    for x in xs
        if iszero(p(x))
            return x
        end
    end
    return nothing
end

function has_root_modulo(p::Polynomial{T, N, I}, k::K) where {T, N, I, K}
    range = zero(K) : (k - one(K))
    for x in Iterators.product(ntuple(_ -> range, Val{N}())...)
        if iszero(p(x) % k)
            return true
        end
    end
    return false
end

function uses_variable(p::Polynomial{T, N, I}, i::Int) where {T, N, I}
    @inbounds for (m, c) in p
        if !iszero(m[i])
            return true
        end
    end
    return false
end

function uses_all_variables(p::Polynomial{T, N, I}) where {T, N, I}
    for i = 1 : N
        if !uses_variable(p, i)
            return false
        end
    end
    return true
end

function is_positive_semidefinite(p::Polynomial{T, N, I}) where {T, N, I}
    _zero = zero(T)
    for (m, c) in p
        if c < _zero || !all(iseven, m)
            return false
        end
    end
    return true
end

function is_negative_semidefinite(p::Polynomial{T, N, I}) where {T, N, I}
    _zero = zero(T)
    for (m, c) in p
        if c > _zero || !all(iseven, m)
            return false
        end
    end
    return true
end

################################################################################

const CANONICAL_VARIABLES = Dict(
    0 => [],
    1 => ["x"],
    2 => ["x", "y"],
    3 => ["x", "y", "z"],
    4 => ["a", "b", "c", "d"],
    5 => ["a", "b", "c", "d", "e"],
    6 => ["a", "b", "c", "d", "e", "f"],
    7 => ["a", "b", "c", "d", "e", "f", "g"],
    8 => ["a", "b", "c", "d", "e", "f", "g", "h"],
    9 => ["a", "b", "c", "d", "e", "f", "g", "h", "i"],
    10 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"],
    11 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"],
    12 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"],
    13 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m"],
    14 => ["a", "b", "c", "d", "e", "f", "g",
           "h", "i", "j", "k", "l", "m", "n"],
    15 => ["a", "b", "c", "d", "e", "f", "g", "h",
           "i", "j", "k", "l", "m", "n", "o"],
    16 => ["a", "b", "c", "d", "e", "f", "g", "h",
           "i", "j", "k", "l", "m", "n", "o", "p"],
    17 => ["a", "b", "c", "d", "e", "f", "g", "h", "i",
           "j", "k", "l", "m", "n", "o", "p", "q"],
    18 => ["a", "b", "c", "d", "e", "f", "g", "h", "i",
           "j", "k", "l", "m", "n", "o", "p", "q", "r"],
    19 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
           "k", "l", "m", "n", "o", "p", "q", "r", "s"],
    20 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
           "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"],
    21 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
           "l", "m", "n", "o", "p", "q", "r", "s", "t", "u"],
    22 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
           "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v"],
    23 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
           "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w"],
    24 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
           "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x"],
    25 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
           "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y"],
    26 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
           "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"]
)

function to_string((m, c)::Monomial{T, N, I}) where {T, N, I}
    if all(iszero(n) for n in m)
        return string(c)
    end
    vars = CANONICAL_VARIABLES[N]
    result = String[]
    needs_star = false
    if isone(c)
        # do nothing
    elseif isone(-c)
        push!(result, "-")
    else
        push!(result, string(c))
        needs_star = true
    end
    for (i, n) in enumerate(m)
        if isone(n)
            if needs_star
                push!(result, "*")
            end
            push!(result, vars[i])
            needs_star = true
        elseif !iszero(n)
            if needs_star
                push!(result, "*")
            end
            push!(result, vars[i])
            push!(result, "^")
            push!(result, string(n))
            needs_star = true
        end
    end
    return join(result)
end

function to_string(p::Polynomial{T, N, I}) where {T, N, I}
    result = String[]
    for (m, c) in p
        if !iszero(c)
            if isempty(result)
                push!(result, to_string(m => c))
            else
                if signbit(c)
                    push!(result, " - ")
                    push!(result, to_string(m => -c))
                else
                    push!(result, " + ")
                    push!(result, to_string(m => c))
                end
            end
        end
    end
    if isempty(result)
        return string(zero(T))
    else
        return join(result)
    end
end

function to_latex((m, c)::Monomial{T, N, I}) where {T, N, I}
    if all(iszero(n) for n in m)
        return string(c)
    end
    vars = CANONICAL_VARIABLES[N]
    result = String[]
    if isone(c)
        # do nothing
    elseif isone(-c)
        push!(result, "-")
    else
        push!(result, string(c))
    end
    for (i, n) in enumerate(m)
        if isone(n)
            push!(result, vars[i])
        elseif !iszero(n)
            push!(result, vars[i])
            push!(result, "^{")
            push!(result, string(n))
            push!(result, "}")
        end
    end
    return join(result)
end

function to_latex(p::Polynomial{T, N, I}) where {T, N, I}
    result = String[]
    for (m, c) in p
        if !iszero(c)
            if isempty(result)
                push!(result, to_latex(m => c))
            else
                if signbit(c)
                    push!(result, " - ")
                    push!(result, to_latex(m => -c))
                else
                    push!(result, " + ")
                    push!(result, to_latex(m => c))
                end
            end
        end
    end
    if isempty(result)
        return "\$0\$"
    else
        return '$' * join(result) * '$'
    end
end

################################################################################

apply_transposition(m::Monomial{T, 0, I}) where {T, I} = m
apply_transposition(m::Monomial{T, 1, I}) where {T, I} = m
apply_cycle(m::Monomial{T, 0, I}) where {T, I} = m
apply_signflip(m::Monomial{T, 0, I}) where {T, I} = m

function apply_transposition(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j, k...), c) = m
    return (j, i, k...) => c
end

function apply_cycle(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j...), c) = m
    return (j..., i) => c
end

function apply_negation((m, c)::Monomial{T, N, I}) where {T, N, I}
    return m => -c
end

function apply_signflip(m::Monomial{T, N, I}) where {T, N, I}
    ((i, j...), c) = m
    return (i, j...) => ifelse(iseven(i), c, -c)
end

################################################################################

function apply_transposition!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_transposition(p[i])
    end
    return p
end

function apply_cycle!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_cycle(p[i])
    end
    return p
end

function apply_negation!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_negation(p[i])
    end
    return p
end

function apply_signflip!(p::Polynomial{T, N, I}) where {T, N, I}
    @inbounds for i = 1 : length(p)
        p[i] = apply_signflip(p[i])
    end
    return p
end

################################################################################

function incr_partition!(x::Vector{T}) where {T}
    _one = one(T)
    @inbounds begin
        n = length(x)
        if n <= 1
            return false
        end
        xn = x[n]
        xn1 = x[n - 1]
        if !iszero(xn1)
            x[n - 1] = xn1 - _one
            x[n] = xn + _one
            return true
        end
        i = n - 2
        while !iszero(i)
            xi = x[i]
            if !iszero(xi)
                x[i] = xi - _one
                if iszero(xn)
                    x[i + 1] += _one
                else
                    x[i + 1] += xn + _one
                    x[n] = zero(T)
                end
                return true
            end
            i -= 1
        end
        return false
    end
end

function integer_partitions(n::T, len::Int) where {T}
    result = Vector{T}[]
    if iszero(n) && iszero(len)
        push!(result, T[])
    elseif !signbit(n) && len >= 1
        p = zeros(T, len)
        @inbounds p[1] = n
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

function ilog2(::Type{T}, n::I) where {T, I}
    result = zero(T)
    one_T = one(T)
    acc = one(I)
    two = acc + acc
    while acc < n
        acc *= two
        result += one_T
    end
    return result
end

function binary_partitions!(result::Vector{Vector{Pair{I, T}}},
                            partition::Vector{Pair{I, T}},
                            n::T, k::I) where {T, I}
    if iszero(n)
        push!(result, copy(partition))
    elseif n > zero(T) && k > zero(I)
        one_T = one(T)
        one_I = one(I)
        j = k - one_I
        while true
            weight = one_T << j
            i = n >> j
            while true
                if iszero(i)
                    break
                end
                push!(partition, j => i)
                binary_partitions!(result, partition, n - i * weight, j)
                Base._deleteend!(partition, 1)
                i -= one_T
            end
            if iszero(j)
                break
            else
                j -= one_I
            end
        end
    end
    return result
end

function binary_partitions(n::T, ::Type{I}) where {T, I}
    return binary_partitions!(
        Vector{Pair{I, T}}[],
        Pair{I, T}[],
        n,
        ilog2(I, n) + one(I)
    )
end

################################################################################

struct HomogeneousPolynomialIterator{T, N, I}
    monomials::Vector{NTuple{N, I}}
    dense_partition::Vector{T}
    sparse_partition::Vector{Pair{Int, T}}
    sign_pattern::Array{UInt, 0} # TODO: make sure this is enough?
    function HomogeneousPolynomialIterator{T, N, I}(
        weight::T, degree::I
    ) where {T, N, I}
        monomials = NTuple{N, I}.(integer_partitions(degree, N))
        dense_partition = zeros(T, length(monomials))
        if length(dense_partition) > 0
            @inbounds dense_partition[1] = weight
            sparse_partition = [1 => weight]
        else
            sparse_partition = Pair{Int, T}[]
        end
        sign_pattern = fill(UInt(0))
        return new(monomials, dense_partition,
                   sparse_partition, sign_pattern)
    end
end

const HPI{T, N, I} = HomogeneousPolynomialIterator{T, N, I}

function reset!(it::HPI{T, N, I}) where {T, N, I}
    dense = it.dense_partition
    sparse = it.sparse_partition
    # note: reduce(+, ...) instead of sum(...) to preserve type
    weight = reduce(+, dense)
    fill!(dense, zero(T))
    empty!(sparse)
    if length(dense) > 0
        @inbounds dense[1] = weight
        push!(sparse, 1 => weight)
    end
    it.sign_pattern[] = UInt(0)
    return it
end

################################################################################

function append_polynomial!(poly::Polynomial{T, N, I},
                            it::HPI{T, N, I}) where {T, N, I}
    s = it.sign_pattern[]
    m = it.monomials
    @inbounds for (i, c) in it.sparse_partition
        push!(poly, m[i] => ifelse(iseven(s), c, -c))
        s >>= 1
    end
    return poly
end

function incr_polynomial!(it::HPI{T, N, I}) where {T, N, I}
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
            if !iszero(c)
                push!(sparse, i => c)
            end
        end
        @assert length(sparse) < 8 * sizeof(UInt)
        return true
    end
end

function get_polynomial(iterators::Vector{HPI{T, N, I}}) where {T, N, I}
    result = Monomial{T, N, I}[]
    for it in iterators
        append_polynomial!(result, it)
    end
    return result
end

function incr_polynomial!(iterators::Vector{HPI{T, N, I}}) where {T, N, I}
    i = length(iterators)
    @inbounds while true
        if iszero(i)
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

struct SignedPartitionIterator
    dense_partition::Vector{Int}
    sparse_partition::Vector{Pair{Int, Int}}
    sign_pattern::Array{UInt, 0}
    function SignedPartitionIterator(n::Int, len::Int)
        dense_partition = zeros(Int, len)
        if len > 0
            @inbounds dense_partition[1] = n
            sparse_partition = [1 => n]
        else
            sparse_partition = Pair{Int, Int}[]
        end
        sign_pattern = fill(UInt(0))
        return new(dense_partition, sparse_partition, sign_pattern)
    end
end

function incr_partition!(it::SignedPartitionIterator)
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
            if !iszero(c)
                push!(sparse, i => c)
            end
        end
        @assert length(sparse) < 8 * sizeof(UInt)
        return true
    end
end

function get_partition(::Val{N}, it::SignedPartitionIterator) where {N}
    result = ntuple(_ -> 0, Val{N}())
    s = it.sign_pattern[]
    @inbounds for (i, c) in it.sparse_partition
        result = Base.setindex(result, ifelse(iseven(s), c, -c), i)
        s >>= 1
    end
    return result
end

function l1_ball(::Val{N}, radius::Int) where {N}
    result = NTuple{N, Int}[]
    it = SignedPartitionIterator(radius, N)
    while true
        push!(result, get_partition(Val{N}(), it))
        if !incr_partition!(it)
            break
        end
    end
    return result
end

################################################################################

end # module DZPolynomials
