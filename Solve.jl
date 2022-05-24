using MathLink
using Printf
using Singular

push!(LOAD_PATH, @__DIR__)
using SystematicDiophantineEquations
using SystematicDiophantineEquations: canonical_variables

################################################################################

function to_smt2(n::Int)
    if signbit(n)
        return "(- $(abs(n)))"
    else
        return string(n)
    end
end

function to_smt2(coeff::Int, powers::NTuple{N, Int},
                 vars::Vector{String}) where {N}
    if N == 0 || sum(powers) == 0
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
    if length(p) > 1
        p_expr = join([to_smt2(c, m, vars) for (c, m) in p], ' ')
        push!(result, "(assert (= (+ $p_expr) 0))")
    elseif length(p) == 1
        push!(result, "(assert (= $(to_smt2(p[1]..., vars)) 0))")
    else
        push!(result, "(assert (= 0 0))")
    end
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

function run_wolfram(p::Polynomial{0})
    if length(p) == 0
        c = 0
    else
        c = p[1][1]
    end
    start = time_ns()
    result = weval(W"Equal"(c, 0))
    stop = time_ns()
    if result == W"True"
        return (SAT, stop - start)
    elseif result == W"False"
        return (UNSAT, stop - start)
    else
        error()
    end
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

function main()
    for height = 1 : 12
        println("----------------------------------------------------------------------------------------")
        @printf("------------------------- ALL HEIGHT %03d DIOPHANTINE EQUATIONS -------------------------\n", height)
        println("----------------------------------------------------------------------------------------")
        println()
        println(" WOLFRAM    CVC5      Z3   YICES MATHSAT |  WOLFRAM     CVC5       Z3    YICES  MATHSAT")
        println("-----------------------------------------+----------------------------------------------+")
        for N = 0 : div(height, 2)
            run_wolfram([(1, ntuple(_ -> 1, Val{N}()))]) # precompile weval
            polys = dedup(all_polynomials(Val{N}(), height), false)
            if length(polys) > 0
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
                        " | ", degrevlex_string(p), " == 0"
                    )
                    flush(stdout)
                end
            end
        end
        println()
    end
end

main()
