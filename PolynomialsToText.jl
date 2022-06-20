using Printf
using Serialization

push!(LOAD_PATH, @__DIR__)
using DZPolynomials

for filename in readdir()
    m = match(r"^All-([0-9]{2})-([0-9]{2})\.jls$", filename)
    if !isnothing(m)
        println("Reading file $filename.")
        flush(stdout)
        h, N = [parse(Int, x) for x in m]
        polys = deserialize(filename)
        println("Writing text file.")
        flush(stdout)
        open(@sprintf("All-%02d-%02d.txt", h, N), "w") do io
            if iszero(N)
                for level in polys[1 : end - 1]
                    @assert isempty(level)
                end
                @assert isone(length(polys[end]))
                println(io, (h, N, 1, 1), " : ", to_string(polys[end][1]))
            else
                for (i, level) in enumerate(polys)
                    @assert !isempty(level)
                    for (j, p) in enumerate(level)
                        println(io, (h, N, i, j), " : ", to_string(p))
                    end
                end
            end
        end
        println("Finished writing text file.")
        flush(stdout)
    end
end
