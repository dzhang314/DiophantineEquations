(* ::Package:: *)

(* :Title: SystematicDiophantineEquations *)
(* :Context: SystematicDiophantineEquations` *)
(* :Author: David K. Zhang *)
(* :Date: 2022-05-21 *)

(* :Package Version: 1.0 *)
(* :Wolfram Language Version: 13.0 *)

(* :Summary: SystematicDiophantineEquations is a Wolfram Language package
             that implements many of the ideas described in the following
             paper: https://arxiv.org/abs/2108.08705 *)

(* :Copyright: (c) 2022 David K. Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. *)

BeginPackage["SystematicDiophantineEquations`"];

AllPolynomials::usage = "";

Begin["`Private`"];
Needs["Developer`"];

exponentPartitions[numVars_Integer, degree_Integer] :=
exponentPartitions[numVars, degree] =
    Join @@ Permutations /@ ToPackedArray@IntegerPartitions[
        degree, {numVars}, Range[0, degree]];

allMonomials[vars_List, degree_Integer] := Times @@@ Map[
    vars^# &,
    exponentPartitions[Length[vars], degree]
];

signFlips[xs_List] := With[
    {signs = Tuples[If[# === 0, {0}, {+1, -1}] & /@ xs]},
    signs * ConstantArray[ToPackedArray[xs], Length[signs]]
];

coefficientPartitions[numTerms_Integer, total_Integer] :=
coefficientPartitions[numTerms, total] =
    Join @@ signFlips /@ exponentPartitions[numTerms, total];

homogeneousPolynomials[vars_List, degree_Integer, k_Integer] := With[
    {monoms = allMonomials[vars, degree]},
    Dot[coefficientPartitions[Length[monoms], k], monoms]
];

AllPolynomials[vars_List, 0, 0] := {0};
AllPolynomials[vars_List, 0, degree_Integer] := {};
AllPolynomials[vars_List, height_Integer, 0] :=
    If[height > 0, {+height, -height}, {}];

AllPolynomials[vars_List, height_Integer, degree_Integer, k_Integer] :=
AllPolynomials[vars, height, degree, k] = If[
    height >= k * 2^degree,
    Join @@ Outer[
        Plus,
        homogeneousPolynomials[vars, degree, k],
        Join @@ Map[
            AllPolynomials[vars, height - k * 2^degree, #] &,
            Range[degree - 1, 0, -1]
        ]
    ],
    {}
];

AllPolynomials[vars_List, height_Integer, degree_Integer] :=
AllPolynomials[vars, height, degree] = If[
    height >= 2^degree,
    Join @@ Map[
        AllPolynomials[vars, height, degree, #] &,
        Range[Floor[height / 2^degree], 1, -1]
    ],
    {}
];

AllPolynomials[vars_List, height_Integer] := Join @@ Map[
    AllPolynomials[vars, height, #] &,
    Range[Floor@Log2[height], 0, -1]
];

End[]; (* `Private` *)
EndPackage[]; (* RungeKuttaUtilities` *)
