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
UniquePolynomials::usage = "";

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

homogeneousPolynomials[{}, 0, 0] = {0};
homogeneousPolynomials[{}, 0, k_Integer] := If[k > 0, {+k, -k}, {}];
homogeneousPolynomials[{}, degree_Integer, 0] = {0};
homogeneousPolynomials[{}, degree_Integer, k_Integer] = {};
homogeneousPolynomials[vars_List, degree_Integer, k_Integer] := With[
    {monoms = allMonomials[vars, degree]},
    Dot[coefficientPartitions[Length[monoms], k], monoms]
];

(* Find all elements of Z[x_1, ..., x_n] of a given height and total degree. *)
AllPolynomials[vars_List, 0, 0] := {0};
AllPolynomials[vars_List, 0, degree_Integer] := {};
AllPolynomials[vars_List, height_Integer, 0] :=
    If[height > 0, {+height, -height}, {}];
AllPolynomials[vars_List, height_Integer, degree_Integer] :=
AllPolynomials[vars, height, degree] = If[
    height >= 2^degree,
    Join @@ Map[
        AllPolynomials[vars, height, degree, #] &,
        Range[Floor[height / 2^degree], 1, -1]
    ],
    {}
];

(* Find all elements of Z[x_1, ..., x_n] of a given height and total degree,
   with a fixed number k of top-degree terms (counted with multiplicity). *)
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

(* Find all elements of Z[x_1, ..., x_n] of a given height. *)
AllPolynomials[vars_List, 0] = {0};
AllPolynomials[vars_List, height_Integer] := Join @@ Map[
    AllPolynomials[vars, height, #] &,
    Range[Floor@Log2[height], 0, -1]
];

UniquePolynomials[{var_}, height_Integer] := With[
    {polys = AllPolynomials[{var}, height]},
    {id = Range[Length[polys]]},
    {indexMap = AssociationThread[polys, id]},
    {negMap = Transpose[{id, ToPackedArray[indexMap /@ -polys]}]},
    {varMap = Transpose[{id, ToPackedArray[
        indexMap /@ (polys /. var -> -var)
    ]}]},
    polys[[Sort[Min /@ ConnectedComponents@Graph@Join[negMap, varMap]]]]
];

UniquePolynomials[vars_List, height_Integer] := With[
    {polys = AllPolynomials[vars, height]},
    {id = Range[Length[polys]]},
    {indexMap = AssociationThread[polys, id]},
    {negMap = Transpose[{id, ToPackedArray[indexMap /@ -polys]}]},
    {varMap = Transpose[{id, ToPackedArray[
        indexMap /@ (polys /. vars[[1]] -> -vars[[1]])
    ]}]},
    {trsMap = Transpose[{id, ToPackedArray[
        indexMap /@ (polys /. {vars[[1]] -> vars[[2]], vars[[2]] -> vars[[1]]})
    ]}]},
    {cycMap = Transpose[{id, ToPackedArray[
        indexMap /@ (polys /. MapThread[Rule, {vars, RotateLeft[vars]}])
    ]}]},
    polys[[Sort[Min /@ ConnectedComponents@Graph@Join[
        negMap, varMap, trsMap, cycMap
    ]]]]
];

End[]; (* `Private` *)
EndPackage[]; (* RungeKuttaUtilities` *)
