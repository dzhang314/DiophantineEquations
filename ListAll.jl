using Printf
using Serialization

push!(LOAD_PATH, @__DIR__)
using DZPolynomials
using DZPolynomialSearch

function inner(::Val{N}, height::T, partition::Vector{Pair{I, T}},
               i::Int, n::Int) where {T, N, I}
    lockname = @sprintf("All-%02d-%02d-%04d.lock", height, N, i)
    donename = @sprintf("All-%02d-%02d-%04d.done", height, N, i)
    tempname = @sprintf("All-%02d-%02d-%04d.temp", height, N, i)
    filename = @sprintf("All-%02d-%02d-%04d.jls", height, N, i)
    if !isfile(lockname) && !isfile(donename)
        touch(lockname)
        println("Working on partition $partition ($i out of $n).")
        flush(stdout)
        polys = all_polynomials(Val{N}(), partition, true)
        serialize(tempname, polys)
        mv(tempname, filename)
        mv(lockname, donename)
    end
end

function main()
    for height = 0 : 99
        for N = 0 : div(height, 2)
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
            for (i, partition) in enumerate(partitions)
                inner(Val{N}(), Int8(height), partition, i, n)
            end
        end
    end
end

main()
