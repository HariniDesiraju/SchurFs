(* ::Package:: *)

BeginPackage["LRCoeffCoproduct`"]


LRCoefficient::usage="LRCoefficient[\[Mu],\[Nu]] enumerats partitions \[Rho] with non-vanishing LR coefficient (\!\(\*SuperscriptBox[\(c\), \(\[Nu]\)]\)\!\(\*SubscriptBox[\()\), \(\[Nu]\[Rho]\)]\) and its value.
If \[Nu] is not included in \[Mu], it returns <|{}-> 0|>, for a technical reason.
LRCoefficient[\[Mu]] enumerats pair of partitions \[Nu],\[Rho] with non-vanishing LR coefficient (\!\(\*SuperscriptBox[\(c\), \(\[Nu]\)]\)\!\(\*SubscriptBox[\()\), \(\[Nu]\[Rho]\)]\) and its value."


LRCoefficientValue::usage="LRCoefficientValue[\[Mu],\[Nu],\[Rho]] gives the integer \!\(\*SubscriptBox[\((\*SuperscriptBox[\(c\), \(\[Mu]\)])\), \(\[Nu]\[Rho]\)]\)."


Begin["Private`"]


(*Given a lattice word, returns the possible next nubers which keeps lattice-ness *)
PossibleNextLatticeNumbers[list_]:=If[list!= {},#,{1}]&@(First/@Select[#,Last[#1]>0&]&@(MapThread[List,{Range[Length[#]],#}]&@(Join[{1},#,{1}]&@((-1)Differences@(Last/@SortBy[#,First]&@Tally[list])))))


(*{i,j} sits in ith row (yokonoretsu) and jth column (tatenoretsu) *) 
boxlist[part_]:=Flatten[#,1]&@Table[{b,a},{b,1,Length[part]},{a,1,part[[b]]}]
boxlist[\[Mu]_,\[Nu]_]:=Complement[boxlist[\[Mu]],boxlist[\[Nu]]]
LRUBsort[list_]:=Sort[list,First[#1]<First[#2]||(First[#1]== First[#2]&&Last[#1]>Last[#2])&]


(*Given a word, put that in the skew diagram \[Lambda]-\[Nu] from right to left (NOT left to right),up to down. Boxes which do not have numbers are not listed. Return as an association*)
(*Functions with arguments \[Mu],\[Nu] are for computations with fixed \[Mu],\[Nu], Functions with \[Mu] are computations with fixed \[Mu], varying \[Nu].*)
PutWordInShape[\[Mu]_,\[Nu]_,word_]:=AssociationThread[Take[#,Length[word]]&@(LRUBsort@boxlist[\[Mu],\[Nu]])-> word]
PutWordInShape[\[Mu]_,word_]:=AssociationThread[Take[#,Length[word]]&@(LRUBsort@boxlist[\[Mu]])-> word]


(*Given above, the number in the above and right box of the most down-left non-empty box*)
NumberAboveRightNextBox[\[Mu]_,word_]:=Module[{boxnumassoc=PutWordInShape[\[Mu],word],nextbox=(LRUBsort@boxlist[\[Mu]])[[Length[word]+1]],tryA0,tryL0,tryA,tryL},
tryA0=boxnumassoc[[Key[(nextbox+{-1,0})]]];
tryL0=boxnumassoc[[Key[(nextbox+{0,1})]]];
tryA=If[MissingQ[tryA0],0,tryA0];
tryL=If[MissingQ[tryL0],Infinity,tryL0];
{tryA,tryL}
]
NumberAboveRightNextBox[\[Mu]_,\[Nu]_,word_]:=Module[{boxnumassoc=PutWordInShape[\[Mu],\[Nu],word],nextbox=(LRUBsort@boxlist[\[Mu],\[Nu]])[[Length[word]+1]],tryA0,tryL0,tryA,tryL},
tryA0=boxnumassoc[[Key[(nextbox+{-1,0})]]];
tryL0=boxnumassoc[[Key[(nextbox+{0,1})]]];
tryA=If[MissingQ[tryA0],0,tryA0];
tryL=If[MissingQ[tryL0],Infinity,tryL0];
{tryA,tryL}
]


(* (To vary \[Nu],) the next number should be 0 if the present box have 0 and not leftmost, can be zero if the box above the present box has 0, or the box is in the upmost row. (0 means the box is skewed away.)
Non zero numbers are inserted so that the obtained tableau is a LR tableu.*)
PossibleNextNumbers[\[Mu]_,\[Nu]_,word_]:=Module[{NARNB=NumberAboveRightNextBox[\[Mu],\[Nu],word],PNLN=PossibleNextLatticeNumbers[word]},
Select[PNLN,NARNB[[1]]<#<= NARNB[[2]]&]]
PossibleNextNumbers[\[Mu]_,word_]:=Module[{NARNB=NumberAboveRightNextBox[\[Mu],word],PNLN=PossibleNextLatticeNumbers[Select[word,#!= 0&]]},
If[NARNB[[2]]==0,{0},#]&@If[NARNB[[1]]==0,{0}~Join~#,#]&@
Select[PNLN,NARNB[[1]]<#<= NARNB[[2]]&]]


PossibleNextWordList[\[Mu]_,\[Nu]_,word_]:=Module[{PNNs=PossibleNextNumbers[\[Mu],\[Nu],word]},
Append[word,#]&/@PNNs]
PossibleNextWordList[\[Mu]_,word_]:=Module[{PNNs=PossibleNextNumbers[\[Mu],word]},
Append[word,#]&/@PNNs]


LRTableauWords[\[Mu]_,\[Nu]_]:=NestWhile[Flatten[(PossibleNextWordList[\[Mu],\[Nu],#1]&)/@#,1]&,{{}},Length[#[[1]]]<  Total[\[Mu]]-Total[\[Nu]]&]
LRTableauWords[\[Mu]_]:=NestWhile[Flatten[(PossibleNextWordList[\[Mu],#1]&)/@#,1]&,{{}},Length[#[[1]]]<  Total[\[Mu]]&]


(*If \[Nu] is included in \[Mu]*)
IncludedQ[\[Mu]_,\[Nu]_]:=Module[{L=Max[Length[\[Mu]],Length[\[Nu]]]},And@@(Thread[PadRight[\[Mu],L]>= PadRight[\[Nu],L]])]


LRTableaus[\[Mu]_,\[Nu]_]:=PutWordInShape[\[Mu],\[Nu],#]&/@LRTableauWords[\[Mu],\[Nu]]
LRTableaus[\[Mu]_]:=PutWordInShape[\[Mu],#]&/@LRTableauWords[\[Mu]]
WeightFromWord[word_]:=Last/@SortBy[#,First]&@Tally[word]
LRCoefficient[\[Mu]_,\[Nu]_]/;IncludedQ[\[Mu],\[Nu]]:=Association@(Tally@(WeightFromWord/@LRTableauWords[\[Mu],\[Nu]])/.{{a_,b_Integer}:>(a-> b)} )
LRCoefficient[\[Mu]_,\[Nu]_]/;!IncludedQ[\[Mu],\[Nu]]:=<|{}-> 0|>
SkewedShape[tableauassoc_]:=Last/@(Tally@(First/@Keys@Select[tableauassoc,#== 0&]))
LRCoefficient[\[Mu]_]:=Association@((Tally@({SkewedShape[#],WeightFromWord[Values[Select[#,#1!= 0&]]]}&/@LRTableaus[\[Mu]]))/.{{a_,b_Integer}:>(a-> b)} )


LRCoefficientValue[\[Mu]_,\[Nu]_,\[Rho]_]:=Module[{tmp},
tmp=LRCoefficient[\[Mu],\[Nu]][[Key[\[Rho]]]];
If[MissingQ[tmp],0,tmp]]


End[]


EndPackage[]
