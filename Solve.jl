using MathLink
using Printf
using Singular

push!(LOAD_PATH, @__DIR__)
using SystematicDiophantineEquations

################################################################################

function canonical_variables(n::Int)
    if n <= 3
        return string.(Vector{Char}("xyz"[1:n]))
    elseif n <= 26
        return string.(Vector{Char}("abcdefghijklmnopqrstuvwxyz"[1:n]))
    else
        error()
    end
end

function to_smt2(n::Int)
    if signbit(n)
        return "(- $(abs(n)))"
    else
        return string(n)
    end
end

function to_smt2(coeff::Int, powers::NTuple{N, Int},
                 vars::Vector{String}) where {N}
    if sum(powers) == 0
        return to_smt2(coeff)
    else
        pieces = [to_smt2(coeff)]
        for (power, var) in zip(powers, vars)
            for _ = 1 : power
                push!(pieces, var)
            end
        end
        return "(* " * join(pieces, ' ') * ")"
    end
end

function to_smt2(p::Polynomial{N}, vars::Vector{String}) where {N}
    result = ["(set-logic QF_NIA)"]
    for var in vars
        push!(result, "(declare-const $var Int)")
    end
    p_expr = join([to_smt2(c, m, vars) for (c, m) in p], ' ')
    push!(result, "(assert (= (+ $p_expr) 0))")
    push!(result, "(check-sat)\n")
    return join(result, '\n')
end

function to_smt2(p::Polynomial{N}) where {N}
    return to_smt2(p, canonical_variables(N))
end

################################################################################

function to_wolfram(p::Polynomial{N}) where {N}
    vars = MathLink.WSymbol.(canonical_variables(N))
    terms = [
        W"Times"(c, W"Apply"(W"Times", W"Power"(vars, m)))
        for (c, m) in p
    ]
    return W"FindInstance"(
        W"Equal"(W"Plus"(terms...), 0),
        vars,
        W"Integers"
    )
end

function run_wolfram(p::Polynomial{N}) where {N}
    wexpr = W"Quiet"(to_wolfram(p))
    start = time_ns()
    result = weval(wexpr)
    stop = time_ns()
    if result.head == W"List"
        if length(result.args) == 0
            return (UNSAT, stop - start)
        else
            return (SAT, stop - start)
        end
    else
        return (UNKNOWN, stop - start)
    end
end

################################################################################

const CVC5_CMD = `timeout 5.0s /home/dkzhang/smt/cvc5`
const Z3_CMD = `timeout 5.0s /home/dkzhang/smt/z3 -smt2 -in`
const YICES_CMD = `timeout 5.0s /home/dkzhang/smt/yices-smt2`
const MATHSAT_CMD = `timeout 5.0s /home/dkzhang/smt/mathsat`

@enum Satisfiability SAT UNSAT UNKNOWN

function interpret_smt2(out::String, err::String)
    if out == "sat\n" && err == ""
        return SAT
    elseif out == "unsat\n" && err == ""
        return UNSAT
    elseif out == "" && err == ""
        return UNKNOWN
    elseif out == "" && err == "cvc5 interrupted by SIGTERM.\n"
        return UNKNOWN
    else
        println("out: ", out)
        println("err: ", err)
        error()
    end
end

function run_smt2(cmd::Cmd, p::Polynomial{N}) where {N}
    inbuf = IOBuffer(to_smt2(p))
    outbuf = IOBuffer()
    errbuf = IOBuffer()
    plan = pipeline(cmd, stdin=inbuf, stdout=outbuf, stderr=errbuf)
    proc = run(plan, wait=false)
    start = time_ns()
    success(proc) # wait for proc to terminate
    stop = time_ns()
    return (interpret_smt2(String(take!(outbuf)), String(take!(errbuf))),
            stop - start)
end

################################################################################

function main(::Val{N}) where {N}
    var_names = canonical_variables(N)
    _, vars = PolynomialRing(ZZ, var_names)
    x = ntuple(i -> (@inbounds vars[i]), Val{N}())
    run_wolfram([(1, ntuple(_ -> 1, Val{N}()))]) # precompile wolfram
    for height = 1 : 99
        polys = unique_nontrivial_polynomials(Val{N}(), height)
        if length(polys) > 0
            println("----------------------------------------------------------------------------------------")
            @printf("---------------------- NON-TRIVIAL HEIGHT %02d %d-VARIABLE EQUATIONS ----------------------\n", height, N)
            println("----------------------------------------------------------------------------------------")
            println()
            println(" WOLFRAM    CVC5      Z3   YICES MATHSAT |  WOLFRAM     CVC5       Z3    YICES  MATHSAT")
            println("-----------------------------------------+----------------------------------------------+")
            for p in polys
                wolfram_result, wolfram_time = run_wolfram(p)
                cvc5_result, cvc5_time = run_smt2(CVC5_CMD, p)
                z3_result, z3_time = run_smt2(Z3_CMD, p)
                yices_result, yices_time = run_smt2(YICES_CMD, p)
                mathsat_result, mathsat_time = run_smt2(MATHSAT_CMD, p)
                println(
                    lpad(wolfram_result, 8),
                    lpad(cvc5_result, 8),
                    lpad(z3_result, 8),
                    lpad(yices_result, 8),
                    lpad(mathsat_result, 8),
                    " | ",
                    @sprintf("%8.6f", 1.0e-9 * wolfram_time),
                    @sprintf("%9.6f", 1.0e-9 * cvc5_time),
                    @sprintf("%9.6f", 1.0e-9 * z3_time),
                    @sprintf("%9.6f", 1.0e-9 * yices_time),
                    @sprintf("%9.6f", 1.0e-9 * mathsat_time),
                    " | ", p(x), " == 0"
                )
                flush(stdout)
            end
            println()
        end
    end
end

main(Val{parse(Int, ARGS[1])}())
