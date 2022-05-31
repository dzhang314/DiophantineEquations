module PolynomialSearch

export dedup, find_polynomials

using DZPolynomials
using Graphs

################################################################################

function dedup(polys::Vector{Polynomial{T, N, I}},
               ::Type{I}, # required to disambiguate types when N = 0
               verbose::Bool=false) where {T, N, I}
    if verbose
        println("Deduplicating $(length(polys)) polynomials.")
        flush(stdout)
    end
    index_dict = Dict{Polynomial{T, N, I}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    if verbose
        println("Constructing symmetry map.")
        flush(stdout)
    end
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
        if verbose && (time_ns() >= last_print + 1000000000)
            println("Computed symmetries of $i polynomials.")
            flush(stdout)
            last_print += 1000000000
        end
    end
    if verbose
        println("Finding connected components of symmetry graph.")
        flush(stdout)
    end
    result = Polynomial{T, N, I}[]
    @inbounds for comp in connected_components(g)
        push!(result, polys[comp[1]])
    end
    if verbose
        println("Finished deduplicating.")
        flush(stdout)
    end
    return result
end

################################################################################

function find_polynomials(::Val{N}, partition::Vector{Pair{I, T}},
                          pre_predicate, post_predicate,
                          verbose::Bool=false) where {T, N, I}
    polys = Polynomial{T, N, I}[]
    if verbose
        println("Working on partition $partition.")
        flush(stdout)
    end
    iterators = [
        HomogeneousPolynomialIterator{T, N, I}(weight, degree)
        for (degree, weight) in partition
    ]
    if verbose
        println("Constructed monomial lists.")
        flush(stdout)
    end
    last_print = time_ns()
    if all(!isempty(it.monomials) for it in iterators)
        while true
            p = get_polynomial(iterators)
            if pre_predicate(p)
                push!(polys, p)
            end
            if !incr_polynomial!(iterators)
                break
            end
            if verbose && (time_ns() >= last_print + 1000000000)
                println("Found $(length(polys)) polynomials so far.")
                flush(stdout)
                last_print += 1000000000
            end
        end
    end
    if verbose
        println("Found $(length(polys)) polynomials before deduplication.")
        flush(stdout)
    end
    uniq = dedup(polys, I, verbose)
    if verbose
        println("Found $(length(uniq)) polynomials after deduplication.")
        flush(stdout)
    end
    result = [p for p in uniq if post_predicate(p)]
    if verbose
        println("Found $(length(result)) polynomials after filtering.")
        flush(stdout)
    end
    return result
end

function find_polynomials(::Val{N}, h::Int, pre_predicate, post_predicate,
                          partition_predicate, verbose::Bool=false) where {N}
    if verbose
        println("Searching for $N-variable polynomials of size $h.")
        flush(stdout)
    end
    partitions = [
        partition
        for partition in binary_partitions(Int8(h), UInt8)
        if partition_predicate(partition)
    ]
    if verbose
        println("Found $(length(partitions)) binary partitions of $h.")
        flush(stdout)
    end
    result = Vector{Polynomial{Int8, N, UInt8}}[]
    for (i, partition) in enumerate(partitions)
        if verbose
            println("Working on partition $i out of $(length(partitions)).")
            flush(stdout)
        end
        chunk = find_polynomials(
            Val{N}(), partition, pre_predicate, post_predicate, verbose
        )
        push!(result, chunk)
        if verbose
            println("Found $(length(result[i])) polynomials in partition $i.")
            flush(stdout)
        end
    end
    return result
end

################################################################################

end # module PolynomialSearch
