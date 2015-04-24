(* ::Package:: *)

Needs["HighEnergyPhysics`fc`"];


(* ::Section::Closed:: *)
(*TIR*)


(* ::Subsection::Closed:: *)
(*Distribute*)


TIR[c_,lp_List,ep_List]/;FreeQ[FCI[c],FCI[FVD[Alternatives@@lp,_]]]:=c;
TIR[Longest[c_] exp_,lp_List,ep_List]/;FreeQ[FCI[c],FCI[FVD[Alternatives@@lp,_]]]:=c TIR[exp,lp,ep];
TIR[Longest[c_.] (exp1_+exp2_),lp_List,ep_List]:=TIR[c exp1,lp,ep]+TIR[c exp2,lp,ep];


(* ::Subsection::Closed:: *)
(*Using TIDL in FeynCalc*)


UsingFeynCalc=True;
UsingFermat=False;
TIRInternal:=If[UsingFermat,TIRFermat,TensorIndexReduce]


TIR[ex_Times,lp_List,ep_List]/;MatchQ[List@@ex,{FCI@FVD[Alternatives@@lp,_]...}]:=Module[{tmp,tmp1,VF},
tmp=ex/.Times[FCI@FVD[lm_,mu_]...]:>VF[{lm,mu}];
tmp=List@@tmp;
tmp1=tmp/.VF->Identity;
tmp=If[UsingFeynCalc,TIDL[tmp1,ep],ex];
If[tmp===ex,tmp=TIRInternal[tmp1,ep]];
Return[tmp];
];


TIR[ex_,lp_List,ep_List]/;MatchQ[ex,FCI@FVD[Alternatives@@lp,_]]:=Module[{tmp,tmp1,VF},
tmp=ex/.FCI@FVD[lm_,mu_]:>VF[{lm,mu}];
tmp=List@@tmp;
tmp1=tmp/.VF->Identity;
tmp=If[UsingFeynCalc,TIDL[tmp1,ep],ex];
If[tmp===ex,tmp=TIRInternal[tmp1,ep]];
Return[tmp];
];


(* ::Section::Closed:: *)
(*TIR Core*)


Clear[CompleteGroup];
CompleteGroup[xs_List,n_Integer]:=Module[{tmp,in,ni,nis},
If[n==1,Return[Transpose[{xs}]]];
nis=Table[ni[in],{in,Length[xs]}];
tmp=nis/.Solve[{Plus@@nis==n,Sequence@@Map[(#>=0)&,nis]},nis,Integers];
tmp=Map[Function[iny,
Flatten[Inner[Function[{x,inx},Array[(x)&,inx]],xs,iny,List]]
],tmp];
tmp=Reverse[tmp];
Return[tmp];
];


Clear[TensorSymmetrize];
(*Version From FeynCalc*)
(*TensorSymmetrize[exp_,idx_List]:=Module[{tmp},
tmp=1/ Factorial[Length[idx]] Plus@@Map[Function[pidx,exp/.Dispatch[Thread[idx->pidx]]], Permutations[idx]];
Return[tmp];
];*)
Unprotect["TIRIdx@"];Clear["TIRIdx@"];Protect["TIRIdx@"];
TensorSymmetrize[exp_,idx0_List]:=Module[{tmp,VF,idx,in},
idx=Table[Symbol[StringJoin["TIRIdx",ToString[in]]],{in,Length[idx0]}];
tmp=Plus@@Permutations[VF@@idx];
VF=Function[Evaluate[idx],Evaluate[exp/.Dispatch[Thread[idx0->idx]]]];
tmp=tmp/.Dispatch[Thread[idx->idx0]];
Clear[VF,idx];
Return[tmp];
];


Clear[SymmetricTensorBasis];
Options[SymmetricTensorBasis]={Dimension->D};
SymmetricTensorBasis[epo_List,lio_List,OptionsPattern[SymmetricTensorBasis]]:=Module[{VF,ep,li,dim,blist,tmp,gterm,gn},
dim=OptionValue[Dimension];
ep=Map[Function[p,VF[Momentum[p,dim]]],epo];
ep=ep/.VF[Momentum[p_,___]]:>p;
li=Map[Function[i,VF[LorentzIndex[i,dim]]],lio];
li=li/.VF[LorentzIndex[i_,___]]:>i;
tmp=CompleteGroup[ep,Length[li]];
blist=Map[Function[moms,Inner[Function[{m,i},
Pair[LorentzIndex[i,dim],Momentum[m,dim]]
],moms,li,Times]],tmp];
For[gn=1,gn<=Floor[Length[li]/2],gn++,
gterm=Times@@Map[Function[lli,FCI[
Function[{x1,x2},Pair[LorentzIndex[x1,dim],LorentzIndex[x2,dim]]]@@lli
]],Partition[Part[li,;;2gn],2]];
If[2gn+1<=Length[li],
tmp=CompleteGroup[ep,Length[li]-2 gn];
tmp=Map[Function[moms,Inner[Function[{m,i},
Pair[LorentzIndex[i,dim],Momentum[m,dim]]
],moms,Part[li,2gn+1;;],Times]],tmp];
tmp=Map[Function[x,gterm x],tmp];
blist=Join[blist,tmp];
,
AppendTo[blist,gterm];
];
];
blist=TensorSymmetrize[blist,li];
Clear[dim,tmp,gterm,gn];
Return[blist];
];


Unprotect[xc];Clear[xc];Protect[xc];
Unprotect[IRTIR];
Clear[IRTIR,IRTIR2FC];
IRTIR2FC[exp_]:=exp/.IRTIR[lpio_,ep_,dim_]:>Apply[Times,Map[Function[mi,
Pair[LorentzIndex[mi[[2]],dim],Momentum[mi[[1]],dim]]
],lpio]];
IRTIR/:MakeBoxes[IRTIR[lpio_,ep_,dim_],TraditionalForm]:=With[{exp=IRTIR2FC[IRTIR[lpio,ep,dim]]},MakeBoxes[exp,TraditionalForm]];
Protect[IRTIR];


Clear[TensorIndexReduce];
(*Special Case*)
Options[TensorIndexReduce]={Dimension->D};
TensorIndexReduce[lpi_List,ep_List,op:OptionsPattern[TensorIndexReduce]]:=TensorIndexReduce[{lpi},ep,op];
(*General Cases*)
TensorIndexReduce[lpio:{_List..},ep_List,op:OptionsPattern[TensorIndexReduce]]:=Module[{in,lpi,xcs,eq1,eq2,blist,tmp,dim,lpr,VF},
ClearSystemCache[];
dim=OptionValue[Dimension];
lpi=Map[Function[pi,VF[Momentum[Part[pi,1],dim],LorentzIndex[Part[pi,2],dim]]],lpio];
lpi=lpi/.VF[Momentum[p_,___],LorentzIndex[i_,___]]:>{p,i};
lpi=Sort[lpi,Function[{e1,e2},Order[Part[e1,1],Part[e2,1]]>0]];
lpi=SplitBy[lpi,First];
If[Length[lpi]>1,
lpr=Union[Flatten[Part[lpi,2;;,All,1]]];
tmp=TensorIndexReduce[First[lpi],Join[ep,lpr],op];
If[Not[FreeQ[tmp,_IRTIR]],Return[IRTIR[lpio,ep,op]]];
tmp=Expand[tmp,_LorentzIndex];
tmp=Distribute[VF[tmp]];
tmp=tmp//.VF[c_ ex_]/;FreeQ[c,Pair[_LorentzIndex,Momentum[Alternatives@@lpr,___]]]:>c VF[ex];
tmp=tmp/.VF[ex_]/;FreeQ[ex,_LorentzIndex]:>ex VF[VF[{}]];
tmp=tmp/.VF[ex_]:>VF[
ex/.Pair[LorentzIndex[i_,dim],Momentum[m_,dim]]/;MemberQ[lpr,m]:>VF[{{m,i}}]
];
tmp=tmp//.VF[x_] VF[y_]:>VF[Join[x,y]];
tmp=tmp/.VF[VF[x_]]:>VF[Join[Flatten[Part[lpi,2;;],1],x]];
tmp=tmp/.VF[x_]:>TensorIndexReduce[x,ep,op];
If[Not[FreeQ[tmp,_IRTIR]],Return[IRTIR[lpio,ep,op]]];
Return[tmp];
];
lpi=First[lpi];
blist=SymmetricTensorBasis[ep,Part[lpi,All,2],Dimension->dim];
xcs=Table[xc[in],{in,Length[blist]}];
eq1=Times@@Map[Function[xpi,
Function[{x1,x2},Pair[LorentzIndex[x2,dim],Momentum[x1,dim]]]@@xpi
],lpi];
eq2=xcs.blist;
tmp=Map[Function[base,Contract[base eq1]==Contract[base eq2]],blist];
tmp=eq2/.Solve3[tmp,xcs];
If[Not[FreeQ[tmp,xc]],Return[IRTIR[lpio,ep,dim]]];
Return[tmp];
];


Clear[TIRFermat];
Options[TIRFermat]={Dimension->D};
TIRFermat[lpio:{_List..},ep_List,op:OptionsPattern[TIRFermat]]:=Module[{lpi,xcs,eq1,eq2,blist,tmp,dim,lpr,VF},
ClearSystemCache[];
dim=OptionValue[Dimension];
lpi=Map[Function[pi,VF[Momentum[Part[pi,1],dim],LorentzIndex[Part[pi,2],dim]]],lpio];
lpi=lpi/.VF[Momentum[p_,___],LorentzIndex[i_,___]]:>{p,i};
lpi=Sort[lpio,Function[{e1,e2},Order[Part[e1,1],Part[e2,1]]>0]];
lpi=SplitBy[lpi,First];
If[Length[lpi]>1,
lpr=Union[Flatten[Part[lpi,2;;,All,1]]];
tmp=TIRFermat[First[lpi],Join[ep,lpr],op];
If[Not[FreeQ[tmp,_IRTIR]],Return[IRTIR[lpio,ep,op]]];
tmp=Expand[tmp,_LorentzIndex];
tmp=Distribute[VF[tmp]];
tmp=tmp//.VF[c_ ex_]/;FreeQ[c,Pair[_LorentzIndex,Momentum[Alternatives@@lpr,___]]]:>c VF[ex];
tmp=tmp/.VF[ex_]/;FreeQ[ex,_LorentzIndex]:>ex VF[VF[{}]];
tmp=tmp/.VF[ex_]:>VF[
ex/.Pair[LorentzIndex[i_,dim],Momentum[m_,dim]]/;MemberQ[lpr,m]:>VF[{{m,i}}]
];
tmp=tmp//.VF[x_] VF[y_]:>VF[Join[x,y]];
tmp=tmp/.VF[VF[x_]]:>VF[Join[Flatten[Part[lpi,2;;],1],x]];
tmp=tmp/.VF[x_]:>TIRFermat[x,ep,op];
If[Not[FreeQ[tmp,_IRTIR]],Return[IRTIR[lpio,ep,op]]];
Return[tmp];
];
lpi=First[lpi];
blist=SymmetricTensorBasis[ep,Part[lpi,All,2],Dimension->dim];
(*Using Fermat*)
eq2=Map[Function[b,blist b//Contract],blist];
eq1=Times@@Map[Function[xpi,
Function[{x1,x2},Pair[LorentzIndex[x2,dim],Momentum[x1,dim]]]@@xpi
],lpi];
eq1=Map[Function[b,eq1 b//Contract],blist];
tmp=FermatRowReduce[eq2,eq1];
tmp=tmp.blist;
Return[tmp];
];


(* ::Section:: *)
(*Using Fermat*)


TIRFermatPath=FileNameJoin[{DirectoryName[$InputFileName],"ferm64","fer64"}];
TIRWorkingPath=Null;


Clear[FermatRun]
FermatRun[fullpath_]:=Module[{rc},
SetDirectory[DirectoryName[fullpath]];
rc=Run["cat "<>fullpath<>"|"<>TIRFermatPath];
ResetDirectory[];
Return[rc];
];


Unprotect[fmMB,fmvD,"fmv@"];
Clear[fmMB,fmvD,"fmv@"];
Protect[fmMB,fmvD,"fmv@"];
FermatCodeFile="fc";
FermatSaveFile="fs";
Clear[FermatRowReduce];
FermatRowReduce[mo_List,bo_List]:=Module[{m,b,sps,fvs,fn,fo,ti,vars,tmp={},line={},rc},
If[TIRWorkingPath===Null,Print["Error: TIRWorkingPath NOT Set!"];Abort[];];
fn=FileNameJoin[{TIRWorkingPath,FermatCodeFile}];
fo=FileNameJoin[{TIRWorkingPath,FermatSaveFile}];
{m,b}={mo,bo};
sps=Cases[{m,b},Pair[_,_],{0,Infinity}]//Union;
fvs=Table[Symbol[StringJoin["fmv",ToString[ti]]],{ti,Length[sps]}];
{m,b}={m,b}/.Dispatch[Thread[sps->fvs]]/.D->fmvD;
vars=Union[Cases[{m,b},_Symbol,Infinity]];
AppendTo[tmp,StringJoin["&(S=",FermatSaveFile,");"]];
AppendTo[tmp,"&_s;"];
AppendTo[tmp,"&(_o=1000);"];
AppendTo[tmp,"&(_t=0);"];
Scan[Function[sym,AppendTo[tmp,StringJoin["&(J=",ToString[sym],");"]]],vars];
rc=Dimensions[m];
AppendTo[tmp,StringJoin["Array fmMB[",ToString[rc[[1]]],",",ToString[rc[[2]]+1],"];"]];
AppendTo[line,"[fmMB]:=[("];
Scan[Function[ele,AppendTo[line,StringJoin[ToString[InputForm[ele]],","]]],Transpose[m],{2}];
Scan[Function[ele,AppendTo[line,StringJoin[ToString[InputForm[ele]],","]]],b];
line[[Length[line]]]=StringTrim[Last[line],","];
AppendTo[line,")];"];
AppendTo[tmp,StringJoin[line]];
(*AppendTo[tmp,"![fermatmb];"];*)
AppendTo[tmp,"Redrowech([fmMB]);"];
AppendTo[tmp,"&(U=1);"];
AppendTo[tmp,"!(&o,[fmMB]);"];
AppendTo[tmp,"&q;"];
AppendTo[tmp,"&x;"];
AppendTo[tmp,""];
Export[fn,tmp,{"Text","Lines"}];
FermatRun[fn];
Unprotect[fmMB];
Clear[fmMB];
Get[fo];
tmp=Table[fmMB[ti,Length[b]+1],{ti,Length[b]}];
tmp=tmp/.fmvD->D/.Dispatch[Thread[fvs->sps]];
Clear[fmMB];
Protect[fmMB];
Return[tmp];
];


(* ::Section:: *)
(*Simple Naming*)


TIRL=TensorIndexReduce;
TIRLF=TIRFermat;
TIRTogether[exp_]:=Collect[exp,_LorentzIndex,Together];
TIRDenominator[ps_List]:=FCI[Det[Outer[SPD,ps,ps]]];
