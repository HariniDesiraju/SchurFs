(* ::Package:: *)

(*Implimented by Kantaro Ohmori, @IAS(princeton) then. 2016-2017*)
(*Partly using codes from http://mathematica.stackexchange.com/questions/22852/looking-for-a-package-regarding-schur-polynomials-and-kostka-numbers *)
BeginPackage["SchurFunction`",{"YDTips`"}];
Needs["LRCoeffCoproduct`"]


SchurF::usage="SchurF[\[Mu],{q1,q2,..,qn,PS[qq1,Q1],...PS[qqn,Qn}] computes the Schur function with specified variables and paritioin.
Here, PS[q,Q] means the set of infinite variables (Q,Qq,\!\(\*SuperscriptBox[\(Qq\), \(2\)]\),\!\(\*SuperscriptBox[\(Qq\), \(3\)]\),...) (Principal Specialization). PS[q]=PS[q,1]. The ordering of variables can be mixed: SchurF[\[Mu],{q,PS[qq],qqq,PS[q4,Q]}] is allowed."
SuperSchurF::usage="SuperSchurF[\[Mu],vars1,vars2] computes the Super Schur function with specified variables and paritioin.
PS[q,Q] can be used both in vars1 and vars2."
SkewSchurF::usage="SkewSchurF[\[Mu],\[Nu],vars] compute the skew Schur function defined by a skew shape \[Mu]/\[Nu]. Details follows that of SchurF."
PS::usage="Principal Specialization"
SkewSuperSchurF::usage="SkewSuperSchurF[\[Mu],\[Nu],vars1,vars2] compute the skew super Schur function defined by a skew shape \[Mu]/\[Nu]. Details follows that of SchurF."
PS::usage="Principal Specialization"


Begin["Private`"]


(*Tips about PS*)
PS[q_]:=PS[q,1]
AllPSQ[list_]:=And@@(MatchQ[Head[#],PS]&/@list)
AllNotPSQ[list_]:=And@@((!MatchQ[Head[#],PS])&/@list)
SomePSQ[list_]:=!AllPSQ[list]&&!AllNotPSQ[list]


(*Hook-Length and Hook-Content formula: http://www.combinatorics.org/ojs/index.php/eljc/article/view/v3i2r14 *)
HLFormula[\[Mu]_,q_,Q_]:=Q^Total[\[Mu]] q^LegTotal[\[Mu]] (Times@@((1-q^Hook[\[Mu],#])^-1&/@Boxset[\[Mu]]))
HCFormula[\[Mu]_,q_,Q1_,Q2_]:=q^LegTotal[\[Mu]] (Times@@(((Q1+Q2 q^Content[#])(1-q^Hook[\[Mu],#])^-1)&/@Boxset[\[Mu]]))


(*Split a symmetric function by LR-coefficients.
Coprodsplit[\[Mu],f,g]=Sum_{\[Nu],\[Rho]}Subscript[(c^\[Mu]), \[Nu]\[Rho]]f[\[Nu]]g[\[Rho]]. *)
Coprodsplitprime[{\[Nu]_,\[Rho]_}-> c_,f_,g_]:=c f[\[Nu]]g[\[Rho]]
Coprodsplit[\[Mu]_,f_,g_]:=Total@(Coprodsplitprime[#,f,g]&/@(Normal@LRCoefficient[\[Mu]]))


(*Schur function with finite variables*)
SchurFFin[part_?(Length[#]>= 1&),vars_List]/;Length[part]<=Length[vars]:=Module[{n=Length[vars],tmp},tmp=C/@Range[n];
Cancel[Det[Outer[Power,tmp,PadLeft[Reverse[part],n]+Range[0,n-1]]]/Det[LinearAlgebra`VandermondeMatrix[tmp]]]/.Thread[tmp:>vars]]
SchurFFin[part_,vars_List]/;Length[part]>Length[vars]:=0
SchurFFin[{},_]:=1


(*Schur function with union of PS's*)
SchurFInf[\[Mu]_,{PS[q_,Q_]}]:=HLFormula[\[Mu],q,Q]
SchurFInf[\[Mu]_,varlist_?(Length[#]>=2&)]:=Coprodsplit[\[Mu],SchurFInf[#,{varlist[[1]]}]&,SchurFInf[#,Drop[varlist,1]]&]


(*SchurF*)
SchurF[\[Mu]_,varlist_?AllPSQ]:=SchurFInf[\[Mu],varlist]
SchurF[\[Mu]_,varlist_?AllNotPSQ]:=SchurFFin[\[Mu],varlist]
SchurF[\[Mu]_,varlist_?SomePSQ]:=Module[{finvars=Select[varlist,!MatchQ[Head[#],PS]&],infvars=Select[varlist,MatchQ[Head[#],PS]&]},Coprodsplit[\[Mu],SchurFFin[#,finvars]&,SchurFInf[#,infvars]&]]


(*Super Schur function with finite variables*)
SuperSchurFFin[\[Mu]_,vars1_List,vars2_List]:=Coprodsplit[\[Mu],SchurFFin[#,vars1]&,SchurFFin[PartitionTranspose[#],vars2]&]


(*Super Schur function with union of PS's*)
SuperSchurFInf[\[Mu]_,{PS[q_,Q1_]},{PS[q_,Q2_]}]:=HCFormula[\[Mu],q,Q1,Q2]
SuperSchurFInf[\[Mu]_,{PS[q1_,Q1_]},{PS[q2_,Q2_]}]/;!MatchQ[q1,q2]:=Coprodsplit[\[Mu],SchurFInf[#,{PS[q1,Q1]}]&,SchurFInf[PartitionTranspose[#],{PS[q2,Q2]}]&]
SuperSchurFInf[\[Mu]_,vars_List,{}]:=SchurFInf[\[Mu],vars]
SuperSchurFInf[\[Mu]_,{},vars_List]:=SchurFInf[PartitionTranspose[\[Mu]],vars]
SuperSchurFInf[\[Mu]_,vars1_,vars2_]/;(Length[vars1]Length[vars2]>0&&(Length[vars1]>= 2||Length[vars2]>= 2)):=Coprodsplit[\[Mu],SuperSchurFInf[#,{vars1[[1]]},{vars2[[1]]}]&,SuperSchurFInf[#,Drop[vars1,1],Drop[vars2,1]]&]


(*SuperSchurF*)
SuperSchurF[\[Mu]_,varlist1_?AllPSQ,varlist2_?AllPSQ]:=SuperSchurFInf[\[Mu],varlist1,varlist2]
SuperSchurF[\[Mu]_,varlist1_?AllNotPSQ,varlist2_?AllNotPSQ]:=SuperSchurFFin[\[Mu],varlist1,varlist2]
SuperSchurF[\[Mu]_,varlist1_,varlist2_]/;SomePSQ[varlist1]||SomePSQ[varlist2]:=Module[{finvars1=Select[varlist1,!MatchQ[Head[#],PS]&],infvars1=Select[varlist1,MatchQ[Head[#],PS]&],finvars2=Select[varlist2,!MatchQ[Head[#],PS]&],infvars2=Select[varlist2,MatchQ[Head[#],PS]&]},Coprodsplit[\[Mu],SuperSchurFFin[#,finvars1,finvars2]&,SuperSchurFInf[#,infvars1,infvars2]&]]


(* Make skew Schur function out of non-skew ones.*)
SkewSumprime[\[Rho]_List->c_,f_]:=c f[\[Rho]]
SkewSum[\[Mu]_List,\[Nu]_List,f_]:=Total@(SkewSumprime[#,f]&/@(Normal@LRCoefficient[\[Mu],\[Nu]]))
SkewSchurF[\[Mu]_List,\[Nu]_List,vars_List]:=SkewSum[\[Mu],\[Nu],SchurF[#,vars]&]
SkewSuperSchurF[\[Mu]_List,\[Nu]_List,vars_List,vars2_List]:=SkewSum[\[Mu],\[Nu],SuperSchurF[#,vars,vars2]&]


End[]


EndPackage[]
