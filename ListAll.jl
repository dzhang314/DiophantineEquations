using Printf
using Serialization

push!(LOAD_PATH, @__DIR__)
using DZPolynomials
using DZPolynomialSearch

function inner(::Val{N}, height::T, partition::Vector{Pair{I, T}},
               i::Int, n::Int) where {T, N, I}
    filename = @sprintf("All-%02d-%02d-%04d.jls", height, N, i)
    @assert !isfile(filename)
    println("Working on partition $partition ($i out of $n).")
    flush(stdout)
    touch(filename)
    polys = all_polynomials(Val{N}(), partition, true)
    rm(filename)
    serialize(filename, polys)
    return filename
end

function main()
    for height = 0 : 99
        for N = 0 : min(div(height, 2), 6)
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
                serialize(dataname, deserialize.(filenames))
                rm.(filenames)
                mv(lockname, donename)
            end
        end
    end
end

main()
