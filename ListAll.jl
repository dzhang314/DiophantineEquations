push!(LOAD_PATH, @__DIR__)
using DZPolynomials

# function canonical_variables(n::Int)
#     if n <= 3
#         return string.(Vector{Char}("xyz"[1:n]))
#     elseif n <= 26
#         return string.(Vector{Char}("abcdefghijklmnopqrstuvwxyz"[1:n]))
#     else
#         error()
#     end
# end

# function to_string((m, c)::Monomial{T, N, I}) where {T, N, I}
#     if all(iszero(n) for n in m)
#         return string(c)
#     end
#     vars = canonical_variables(N)
#     result = String[]
#     needs_star = false
#     if isone(c)
#         # do nothing
#     elseif isone(-c)
#         push!(result, "-")
#     else
#         push!(result, string(c))
#         needs_star = true
#     end
#     for (i, n) in enumerate(m)
#         if isone(n)
#             if needs_star
#                 push!(result, "*")
#             end
#             push!(result, vars[i])
#             needs_star = true
#         elseif !iszero(n)
#             if needs_star
#                 push!(result, "*")
#             end
#             push!(result, vars[i])
#             push!(result, "^")
#             push!(result, string(n))
#             needs_star = true
#         end
#     end
#     return join(result)
# end

# function to_string(p::Polynomial{T, N, I}) where {T, N, I}
#     result = String[]
#     for (m, c) in p
#         if !iszero(c)
#             if isempty(result)
#                 push!(result, to_string(m => c))
#             else
#                 if signbit(c)
#                     push!(result, " - ")
#                     push!(result, to_string(m => -c))
#                 else
#                     push!(result, " + ")
#                     push!(result, to_string(m => c))
#                 end
#             end
#         end
#     end
#     if isempty(result)
#         return string(zero(T))
#     else
#         return join(result)
#     end
# end

################################################################################

using Graphs

function dedup(polys::Vector{Polynomial{T, N, I}}, ::Type{I}) where {T, N, I}
    println("Deduplicating $(length(polys)) polynomials.")
    flush(stdout)
    index_dict = Dict{Polynomial{T, N, I}, Int}()
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
    result = Polynomial{T, N, I}[]
    @inbounds for comp in connected_components(g)
        push!(result, polys[comp[1]])
    end
    println("Finished deduplicating.")
    flush(stdout)
    return result
end

function all_polynomials(::Val{N},
                         partition::Vector{Pair{I, T}}) where {T, N, I}
    last_print = time_ns()
    result = Polynomial{T, N, I}[]
    iterators = [
        HomogeneousPolynomialIterator{T, N, I}(weight, degree)
        for (degree, weight) in partition
    ]
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
    return dedup(result, I)
end

using Printf
using Serialization

function inner(::Val{N}, height::T, partition::Vector{Pair{I, T}},
               i::Int, n::Int) where {T, N, I}
    filename = @sprintf("All-%02d-%02d-%04d.jls", height, N, i)
    @assert !isfile(filename)
    println("Working on partition $partition ($i out of $n).")
    flush(stdout)
    touch(filename)
    polys = all_polynomials(Val{N}(), partition)
    rm(filename)
    serialize(filename, polys)
    return filename
end

function main()
    for height = 0 : 99
        for N = 0 : div(height, 2)
            dataname = @sprintf("All-%02d-%02d.jls", height, N)
            lockname = @sprintf("All-%02d-%02d.lock", height, N)
            donename = @sprintf("All-%02d-%02d.done", height, N)
            if !isfile(lockname) && !isfile(donename)
                touch(lockname)
                println("Searching for all $N-variable polynomials of height $height.")
                flush(stdout)
                partitions = [
                    partition
                    for partition in binary_partitions(Int8(height), UInt8)
                    if sum([i * j for (i, j) in partition]) >= N
                ]
                n = length(partitions)
                println("Found $n binary partitions of $height.")
                flush(stdout)
                filenames = String[]
                for (i, partition) in enumerate(partitions)
                    push!(filenames, inner(Val{N}(), Int8(height), partition, i, n))
                end
                serialize(dataname, reduce(vcat, deserialize.(filenames)))
                rm.(filenames)
                mv(lockname, donename)
            end
        end
    end
end

main()
