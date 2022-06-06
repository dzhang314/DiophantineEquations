using Primes
using Printf
using Serialization

push!(LOAD_PATH, @__DIR__)
using DZPolynomials

cd("/Users/dzhang314/DiophantineEquations")

function load_polynomials(::Val{N}, height::Int) where {N}
    result = Dict{NTuple{4, Int}, Polynomial{Int8, N, UInt8}}()
    for h = 2 * N : height
        polys = deserialize(@sprintf("All-%02d-%02d.jls", h, N))
        for (i, level) in enumerate(polys)
            for (j, p) in enumerate(level)
                result[(h, N, i, j)] = p
            end
        end
    end
    return result
end

function analyze_polynomials(::Val{N}, h::Int) where {N}
    polys = load_polynomials(Val{N}(), h)
    solved = Dict{NTuple{4, Int}, NTuple{N, Int}}()
    refuted = Dict{NTuple{4, Int}, Int}()
    radius = 0
    modulus = 2
    last_solve_time = zero(UInt)
    last_refute_time = one(UInt)
    while true
        if last_solve_time < last_refute_time
            start = time_ns()
            ball = l1_ball(Val{N}(), radius)
            queue = Dict{NTuple{4, Int}, NTuple{N, Int}}()
            for (id, p) in polys
                root = find_root(p, ball)
                if !isnothing(root)
                    solved[id] = root
                    queue[id] = root
                end
            end
            if !isempty(queue)
                println("Solved $(length(queue)) equations at radius $radius.")
                flush(stdout)
                serialize(@sprintf("Solved-%02d-%02d-%012d.jls", N, h, radius), queue)
                for (id, _) in queue
                    delete!(polys, id)
                end
                println("$(length(polys)) equations left.")
                flush(stdout)
            else
                println("Tried radius $radius; no equations solved.")
                println("$(length(polys)) equations left.")
                flush(stdout)
            end
            stop = time_ns()
            last_solve_time = stop - start
            radius += 1
        else
            start = time_ns()
            queue = Set{NTuple{4, Int}}()
            for (id, p) in polys
                if !has_root_modulo(p, modulus)
                    refuted[id] = modulus
                    push!(queue, id)
                end
            end
            if !isempty(queue)
                println("Proved $(length(queue)) equations unsolvable at modulus $modulus.")
                flush(stdout)
                serialize(@sprintf("Refuted-%02d-%02d-%012d.jls", N, h, modulus), queue)
                for id in queue
                    delete!(polys, id)
                end
                println("$(length(polys)) equations left.")
                flush(stdout)
            else
                println("Tried modulus $modulus; no equations proven unsolvable.")
                println("$(length(polys)) equations left.")
                flush(stdout)
            end
            stop = time_ns()
            last_refute_time = stop - start
            while true
                modulus += 1
                if isprime(radical(modulus))
                    break
                end
            end
        end
    end
end

analyze_polynomials(Val{parse(Int, ARGS[1])}(), parse(Int, ARGS[2]))
