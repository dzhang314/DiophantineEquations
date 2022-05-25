using Graphs
using Printf
using Serialization

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

struct HomogeneousPolynomialIterator{N}
    monomials::Vector{NTuple{N, Int}}
    dense_partition::Vector{Int}
    sparse_partition::Vector{Tuple{Int, Int}}
    sign_pattern::Array{UInt, 0}
    function HomogeneousPolynomialIterator{N}(weight::Int,
                                              degree::Int) where {N}
        monomials = NTuple{N, Int}.(integer_partitions(degree, N))
        dense_partition = zeros(Int, length(monomials))
        if length(dense_partition) > 0
            dense_partition[1] = weight
            sparse_partition = [(weight, 1)]
        else
            sparse_partition = Tuple{Int, Int}[]
        end
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
    empty!(sparse)
    if length(dense) > 0
        dense[1] = weight
        push!(sparse, (weight, 1))
    end
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

apply_transposition(m::Monomial{0}) = m
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

apply_cycle(m::Monomial{0}) = m

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

apply_signflip(m::Monomial{0}) = m

function apply_signflip((c, (i, j...))::Monomial{N}) where {N}
    return (ifelse(i & 1 == 0, c, -c), (i, j...))
end

function apply_signflip!(p::Polynomial{N}) where {N}
    @inbounds for i = 1 : length(p)
        p[i] = apply_signflip(p[i])
    end
    return p
end

function dedup(polys::Vector{Polynomial{N}}) where {N}
    println("Deduplicating $(length(polys)) polynomials.")
    flush(stdout)
    index_dict = Dict{Polynomial{N}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    println("Constructing symmetry map.")
    flush(stdout)
    last_print = time_ns()
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
        if time_ns() >= last_print + 1000000000
            println("Computed symmetries of $i polynomials.")
            flush(stdout)
            last_print += 1000000000
        end
    end
    println("Finding connected components of symmetry graph.")
    flush(stdout)
    result = Polynomial{N}[]
    @inbounds for comp in connected_components(g)
        push!(result, polys[comp[1]])
    end
    return result
end

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

function all_polynomials(::Val{N}, partition::Vector{Tuple{Int, Int}}) where {N}
    println("Working on partition $partition.")
    flush(stdout)
    last_print = time_ns()
    iterators = [HPI{N}(weight, degree) for (weight, degree) in partition]
    result = Polynomial{N}[]
    if all(length(it.monomials) > 0 for it in iterators)
        while true
            p = get_polynomial(iterators)
            if uses_all_variables(p)
                push!(result, p)
            end
            if !incr_polynomial!(iterators)
                break
            end
            if time_ns() >= last_print + 1000000000
                println("Found $(length(result)) polynomials so far.")
                flush(stdout)
                last_print += 1000000000
            end
        end
    end
    println("Found $(length(result)) polynomials in total.")
    flush(stdout)
    return dedup(result)
end

function inner(::Val{N}, height::Int, partition::Vector{Tuple{Int, Int}}, i::Int, n::Int) where {N}
    filename = @sprintf("/home/dkzhang/DiophantineEquations/All-%02d-%02d-%04d.jls", height, N, i)
    if !isfile(filename)
        println("Working on partition $partition ($i out of $n).")
        flush(stdout)
        touch(filename)
        polys = all_polynomials(Val{N}(), partition)
        rm(filename)
        serialize(filename, polys)
    end
end

function main()
    for height = 20 : 99
        for N = 0 : div(height, 2)
            lockname = @sprintf("/home/dkzhang/DiophantineEquations/All-%02d-%02d.lock", height, N)
            donename = @sprintf("/home/dkzhang/DiophantineEquations/All-%02d-%02d.done", height, N)
            if !isfile(lockname) && !isfile(donename)
                touch(lockname)
                println("Searching for all $N-variable polynomials of height $height.")
                flush(stdout)
                partitions = [
                    partition
                    for partition in power_of_two_partitions(height)
                    if sum([i * j for (i, j) in partition]) >= N
                ]
                n = length(partitions)
                println("Found $n binary partitions of $height.")
                flush(stdout)
                for i = 1 : n
                    inner(Val{N}(), height, partitions[i], i, n)
                    GC.gc(true)
                end
                mv(lockname, donename)
            end
        end
    end
end

main()
