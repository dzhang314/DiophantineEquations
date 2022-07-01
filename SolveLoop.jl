using Primes
using Printf
using Serialization

push!(LOAD_PATH, @__DIR__)
using DZPolynomials

const ID = NTuple{4, Int}

function load_polynomials(::Val{N}, h::Int) where {N}
    result = Dict{ID, Polynomial{Int8, N, UInt8}}()
    polys = deserialize(@sprintf("All-%02d-%02d.jls", h, N))
    for (i, level) in enumerate(polys)
        for (j, p) in enumerate(level)
            result[(h, N, i, j)] = p
        end
    end
    return result
end

function analyze_polynomials(::Val{N}, h::Int, max_radius::T,
                             max_modulus::U) where {N, T, U}
    polys = load_polynomials(Val{N}(), h)
    solved = Dict{ID, NTuple{N, T}}()
    refuted = Dict{ID, U}()
    radius = zero(T)
    modulus = one(U) + one(U)
    last_solve_time = zero(UInt)
    last_refute_time = one(UInt)
    while !isempty(polys)
        if last_solve_time < last_refute_time
            start = time_ns()
            ball = l1_ball(Val{N}(), radius::T)
            queue = ID[]
            for (id, p) in polys
                root = find_root(p, ball)
                if !isnothing(root)
                    solved[id] = root::NTuple{N, T}
                    push!(queue, id)
                end
            end
            if !isempty(queue)
                println("Solved $(length(queue)) equations ",
                        "at radius $radius.")
                flush(stdout)
                for id in queue
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
            radius += one(T)
            if radius > max_radius
                last_solve_time = typemax(UInt)
                if last_refute_time == typemax(UInt)
                    break
                end
            end
        else
            start = time_ns()
            queue = ID[]
            for (id, p) in polys
                if !has_root_modulo(p, modulus::U)
                    refuted[id] = modulus
                    push!(queue, id)
                end
            end
            if !isempty(queue)
                println("Proved $(length(queue)) equations ",
                        "unsolvable at modulus $modulus.")
                flush(stdout)
                for id in queue
                    delete!(polys, id)
                end
                println("$(length(polys)) equations left.")
                flush(stdout)
            else
                println("Tried modulus $modulus; ",
                        "no equations proven unsolvable.")
                println("$(length(polys)) equations left.")
                flush(stdout)
            end
            stop = time_ns()
            last_refute_time = stop - start
            while true
                modulus += one(U)
                if isprime(radical(modulus))
                    break
                end
            end
            if modulus > max_modulus
                last_refute_time = typemax(UInt)
                if last_solve_time == typemax(UInt)
                    break
                end
            end
        end
    end
    return (solved, refuted, polys)
end

function main(::Val{N}, radius::BigInt, modulus::BigInt) where {N}
    for h = 0 : 999
        if isfile(@sprintf("All-%02d-%02d.jls", h, N))
            solved, refuted, polys = analyze_polynomials(
                Val{N}(), h, radius, modulus
            )
            if !isempty(solved)
                filename = @sprintf("Solved-%02d-%02d-%08d", h, N, radius)
                serialize(filename * ".jls", solved)
                open(filename * ".txt", "w") do io
                    for (id, sol) in sort!(collect(solved))
                        println(io, id, " : ", sol)
                    end
                end
            end
            if !isempty(refuted)
                filename = @sprintf("Refuted-%02d-%02d-%08d", h, N, modulus)
                serialize(filename * ".jls", refuted)
                open(filename * ".txt", "w") do io
                    for (id, m) in sort!(collect(refuted))
                        println(io, id, " : ", m)
                    end
                end
            end
            if !isempty(polys)
                filename = @sprintf("Unknown-%02d-%02d-%08d", h, N, modulus)
                serialize(filename * ".jls", polys)
                open(filename * ".txt", "w") do io
                    for (id, p) in sort!(collect(polys))
                        println(io, id, " : ", to_string(p))
                    end
                end
            end
        end
    end
end

main(
    Val{parse(Int, ARGS[1])}(),
    parse(BigInt, ARGS[2]),
    parse(BigInt, ARGS[3])
)
