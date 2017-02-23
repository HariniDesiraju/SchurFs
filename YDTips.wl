(* ::Package:: *)

BeginPackage["YDTips`"]


PartitionTranspose::usage="PartitionTranspose[\[Mu]] gives the transpose of \[Mu]."
Boxset::usage="Set of Box of a partition."
Arm::usage="Arm[\[Mu],s] gives arm length of s in \[Mu]."
Leg::usage="Leg[\[Mu],s] gives arm length of s in \[Mu]."
Hook::usage="hook."
Content::usage="(j-i) of {i,j}. Here, {i,j} means the box in ith row and jth column."
LegTotal::usage="total of leg length of all boxes in a parition."
IntegerPartitionsnomore::usage="IntegerPartitionsnomore[N] enumerates all the paritions with size no more than N.
IntegerPartitionsnomore[N,k] enumerates all the paritionis with size no more than N and length no more than k."


Begin["Private`"]


validPartitionQ[part_]:=VectorQ[part,(IntegerQ[#]&&NonNegative[#])&]&&Apply[GreaterEqual,part]


Boxset[part_?validPartitionQ]:=Flatten[#,1]&@Table[{j,i},{j,1,Length[part]},{i,1,part[[j]]}]


PartitionTranspose[part_?(validPartitionQ[#]&&Length[#]>=1&) ]:=Table[Length[Select[part,#>= i&]],{i,1,Max[part]}]
PartitionTranspose[{}]:={}


Arm[part_?validPartitionQ,{i_,j_}]:=PadRight[part,i][[i]]-j


Leg[part_?validPartitionQ,{i_,j_}]:=Arm[PartitionTranspose[part],{j,i}];


Hook[part_?validPartitionQ,box_]:=Arm[part,box]+Leg[part,box]+1;


Content[{i_,j_}]:=(j-i)


LegTotal[part_?validPartitionQ]:=Sum[(i-1)part[[i]],{i,1,Length[part]}]


IntegerPartitionsnomore[N_]:=Flatten[#,1]&@Table[IntegerPartitions[i],{i,0,N}]
IntegerPartitionsnomore[N_,k_]:=Flatten[#,1]&@Table[IntegerPartitions[i,k],{i,0,N}]


End[]
EndPackage[]
