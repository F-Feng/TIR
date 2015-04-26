(* ::Package:: *)

(* ::Section:: *)
(*TIR Package*)


BeginPackage["TIR`"];


Unprotect[TIRIR];
Clear[TIRIR];
TIRIR/:MakeBoxes[TIRIR[lpio_,ep_,dim_],TraditionalForm]:=With[{exp=Apply[Times,Map[Function[mi,TIRFV[mi[[1]],mi[[2]]]],lpio]]},MakeBoxes[exp,TraditionalForm]];
Protect[TIRIR];


TIRDimension::usage="Dimension in TIR, Default is D";
TIRFV::usage="Four Vector in TIR, TIRFV[p,m] with p Momentum and m Lorentz Index";
TIRSP::usage="Scalar Product in TIR, TIRSP[p,q] with p and q Momentum";
ClearTIRSP::usage="Remove All Asigned Scalar Product";
TIRMT::usage="Metric Tensor in TIR, TIRMT[m,n] with m and n Lorentz Index";
TIRIR::usage="TIR IRreducible Expression";
TIR::usage="TIR: Tensor Index Reduce, TIR[{{q1,m1},{q2,m2},...},{p1,p2,...}] with qi Loop Momentum and pi External Momentum";


TIRLinearSolver::usage="The Linear Equation Solver in TIR: TIRFermat, TIRMMA, TIRFCS3";
TIRFermat::usage="Linear Equation Solve in TIR Using Fermat";
TIRMMA::usage="Linear Equation Solve in TIR Using Mathematica LinearSolver";
TIRFCS3::usage="Linear Equation Solve in TIR Using Solve3 from FeynCalc";


TIRTogether::usage="TIRTogether: Collect TIRFV Terms in TIR";
TIRDenominator::usage="TIRDenominator[{p1,p2,...}] - Gram Determinant for External Momenta {p1,p2,...}";
TIRDenominator::Zero="The TIRDenominator is ZERO, and TIR can not determinate the Reduction Uniquely!";
TIRFermatPath::usage="TIRFermatPath: Fermat Path Used in TIR";


SymmetricTensorBasis::usage="SymmetricTensorBasis[ps_List,li_List] with ps External Momentum List and li Lorentz Index List"


Unprotect[fmMB,fmvD,"fmv@"];
Clear[fmMB,fmvD,"fmv@"];
Protect[fmMB,fmvD,"fmv@"];
fmMB::usage="MB-Matrix M and Vector B in Fermat";
fmvD::usage="The TIRDimension in Fermat";


Begin["`Private`"];


(* ::Subsection::Closed:: *)
(*TIR-SP/MT/FV*)


SetAttributes[TIRMT,Orderless];
SetAttributes[TIRSP,Orderless];


TIRMT/:MakeBoxes[TIRMT[mu_,nu_], TraditionalForm ]:=SuperscriptBox["g", RowBox[{MakeBoxes[mu, TraditionalForm],MakeBoxes[nu, TraditionalForm]}]];


TIRSP/:MakeBoxes[TIRSP[p_, p_],TraditionalForm]:=SuperscriptBox[MakeBoxes[p,TraditionalForm],2];
TIRSP/:MakeBoxes[TIRSP[p_, q_],TraditionalForm]:=RowBox[{MakeBoxes[p, TraditionalForm], "\[CenterDot]",MakeBoxes[q, TraditionalForm]}]


TIRFV/:MakeBoxes[TIRFV[p_,mu_],TraditionalForm]:=SuperscriptBox[MakeBoxes[p,TraditionalForm],MakeBoxes[mu,TraditionalForm]];


TIRMT/:TIRMT[mu_,mu_]:=TIRDimension;
TIRMT/:TIRMT[mu_,nu_]^2:=TIRDimension;
TIRMT/:TIRMT[mu_,nu_] TIRFV[p_,mu_]:=TIRFV[p,nu]


TIRFV/:TIRFV[p_,mu_] TIRFV[q_,mu_]:=TIRSP[p,q]
TIRFV/:TIRFV[p_,mu_]^2:=TIRSP[p,p]
TIRFV[p_+q_,mu_]:=TIRFV[p,mu]+TIRFV[q,mu]


TIRSP[p_,q1_+q2_]:=TIRSP[p,q1]+TIRSP[p,q2]


(* ::Subsection::Closed:: *)
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


Unprotect["TIRIdx@"];Clear["TIRIdx@"];Protect["TIRIdx@"];
Clear[TensorSymmetrize];
TensorSymmetrize[exp_,idx0_List]:=Module[{tmp,VF,idx,in},
idx=Table[Symbol[StringJoin["TIRIdx",ToString[in]]],{in,Length[idx0]}];
tmp=Plus@@Permutations[VF@@idx];
VF=Function[Evaluate[idx],Evaluate[exp/.Dispatch[Thread[idx0->idx]]]];
tmp=tmp/.Dispatch[Thread[idx->idx0]];
Clear[VF,idx];
Return[tmp];
];


Clear[SymmetricTensorBasis];
SymmetricTensorBasis[epo_List,lio_List]:=Module[{VF,ep,li,blist,tmp,gterm,gn},
ep=epo;
li=lio;
tmp=CompleteGroup[ep,Length[li]];
blist=Map[Function[moms,Inner[Function[{m,i},TIRFV[m,i]],moms,li,Times]],tmp];
For[gn=1,gn<=Floor[Length[li]/2],gn++,
gterm=Times@@Map[Function[lli,Function[{x1,x2},TIRMT[x1,x2]]@@lli],Partition[Part[li,;;2gn],2]];
If[2gn+1<=Length[li],
tmp=CompleteGroup[ep,Length[li]-2 gn];
tmp=Map[Function[moms,Inner[Function[{m,i},TIRFV[m,i]],moms,Part[li,2gn+1;;],Times]],tmp];
tmp=Map[Function[x,gterm x],tmp];
blist=Join[blist,tmp];
,
AppendTo[blist,gterm];
];
];
blist=TensorSymmetrize[blist,li];
Clear[tmp,gterm,gn];
Return[blist];
];


Clear[TIR];
TIR[lpi_List,ep_List]:=TIR[{lpi},ep];
TIR[lpio:{_List..},ep_List]:=Module[{lpi,eq1,eq2,blist,tmp,lpr,VF},
If[TIRDenominator[ep]===0,Message[TIRDenominator::Zero];Return[TIRIR[lpio,ep]]];
ClearSystemCache[];
lpi=lpio;
lpi=Sort[lpi,Function[{e1,e2},Order[Part[e1,1],Part[e2,1]]>0]];
lpi=SplitBy[lpi,First];
If[Length[lpi]>1,
lpr=Union[Flatten[Part[lpi,2;;,All,1]]];
tmp=TIR[First[lpi],Join[ep,lpr]];
If[Not[FreeQ[tmp,_TIRIR]],Return[TIRIR[lpio,ep]]];
tmp=Expand[tmp,_TIRFV];
tmp=Distribute[VF[tmp]];
tmp=tmp//.VF[c_ ex_.]/;FreeQ[c,TIRFV[Alternatives@@lpr,_]]:>c VF[ex];
tmp=tmp/.VF[1]:>VF[VF[{}]];
tmp=tmp/.VF[ex_]:>VF[
ex/.TIRFV[m_,i_]/;MemberQ[lpr,m]:>VF[{{m,i}}]
];
tmp=tmp//.VF[x_] VF[y_]:>VF[Join[x,y]];
tmp=tmp/.VF[VF[x_]]:>VF[Join[Flatten[Part[lpi,2;;],1],x]];
tmp=tmp/.VF[x_]:>TIR[x,ep];
If[Not[FreeQ[tmp,_TIRIR]],Return[TIRIR[lpio,ep]]];
Return[tmp];
];
lpi=First[lpi];
blist=SymmetricTensorBasis[ep,Part[lpi,All,2]];
eq2=Map[Function[b,Expand[blist b,_TIRFV|_TIRMT]],blist];
On[Assert];Assert[FreeQ[eq2,_TIRFV|_TIRMT]];
eq1=Times@@Map[Function[xpi,
Function[{x1,x2},TIRFV[x1,x2]]@@xpi
],lpi];
eq1=Map[Function[b,Expand[eq1 b,_TIRFV|_TIRMT]],blist];
tmp=TIRLinearSolver[eq2,eq1];(*Use Different Linear Solver*)
tmp=tmp.blist;
Return[tmp];
];


(* ::Subsection:: *)
(*TIRLinearSolver*)


(* ::Subsubsection:: *)
(*TIRMMA*)


Clear[TIRMMA];
TIRMMA[m_,b_]:=LinearSolve[m,b];


(* ::Subsubsection:: *)
(*TIRFC*)


Clear[TIRFC3];
TIRFC3[m_,b_]:=LinearSolve[m,b];


(* ::Subsubsection:: *)
(*TIRFermat*)


TIRFermatPath=FileNameJoin[{DirectoryName[$InputFileName],Switch[$OperatingSystem,"MacOSX","ferm64","Linux","ferl64"],"fer64"}];


Clear[TIRFermat];
TIRFermat[mo_List,bo_List]:=Module[{m,b,sps,fvs,wp,ti,vars,tmp={},line={},rc},
{m,b}={mo,bo};
sps=Cases[{m,b},TIRSP[_,_],{0,Infinity}]//Union;
fvs=Table[Symbol[StringJoin["fmv",ToString[ti]]],{ti,Length[sps]}];
{m,b}={m,b}/.Dispatch[Thread[sps->fvs]]/.D->fmvD;
vars=Union[Cases[{m,b},_Symbol,Infinity]];
AppendTo[tmp,"&(S=out);"];
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
wp=CreateDirectory[];
SetDirectory[wp];
Export["in",tmp,{"Text","Lines"}];
Run["cat "<>FileNameJoin[{wp,"in"}]<>"|"<>TIRFermatPath];
ResetDirectory[];
Unprotect[fmMB];
Clear[fmMB];
Get[FileNameJoin[{wp,"out"}]];
Quiet[DeleteDirectory[wp,DeleteContents->True]];
tmp=Table[fmMB[ti,Length[b]+1],{ti,Length[b]}];
tmp=tmp/.fmvD->TIRDimension/.Dispatch[Thread[fvs->sps]];
Clear[fmMB];
Protect[fmMB];
Return[tmp];
];


(* ::Subsection::Closed:: *)
(*Others*)


TIRDimension=D;
TIRLinearSolver=TIRFermat;


TIRTogether[exp_]:=Collect[exp,_TIRFV,Together];
TIRDenominator[ps_List]:=Det[Outer[TIRSP,ps,ps]];


SPInitlDownValues=DownValues[TIRSP];
SPInitlUpValues=UpValues[TIRSP];
ClearTIRSP[]:=With[{},
DownValues[TIRSP]=SPInitlDownValues;
UpValues[TIRSP]=SPInitlUpValues;
];


End[];


EndPackage[];


(* ::Section:: *)
(*TIRFC*)


(* ::Subsection:: *)
(*Distribute*)


TIRFC[c_,lp_List,ep_List]/;FreeQ[FCI[c],FCI[FVD[Alternatives@@lp,_]]]:=c;
TIRFC[Longest[c_] exp_,lp_List,ep_List]/;FreeQ[FCI[c],FCI[FVD[Alternatives@@lp,_]]]:=c TIR[exp,lp,ep];
TIRFC[Longest[c_.] (exp1_+exp2_),lp_List,ep_List]:=TIR[c exp1,lp,ep]+TIR[c exp2,lp,ep];


(* ::Subsection:: *)
(*Using TIDL in FeynCalc*)


TIRFC[ex_Times,lp_List,ep_List]/;MatchQ[List@@ex,{FCI@FVD[Alternatives@@lp,_]...}]:=Module[{tmp,tmp1,VF},
tmp=ex/.Times[FCI@FVD[lm_,mu_]...]:>VF[{lm,mu}];
tmp=List@@tmp;
tmp1=tmp/.VF->Identity;
tmp=If[UsingFeynCalc,TIDL[tmp1,ep],ex];
If[tmp===ex,tmp=TIRInternal[tmp1,ep]];
Return[tmp];
];


TIRFC[ex_,lp_List,ep_List]/;MatchQ[ex,FCI@FVD[Alternatives@@lp,_]]:=Module[{tmp,tmp1,VF},
tmp=ex/.FCI@FVD[lm_,mu_]:>VF[{lm,mu}];
tmp=List@@tmp;
tmp1=tmp/.VF->Identity;
tmp=If[UsingFeynCalc,TIDL[tmp1,ep],ex];
If[tmp===ex,tmp=TIRInternal[tmp1,ep]];
Return[tmp];
];


(*TIRIR2FC[exp_]:=exp/.TIRIR[lpio_,ep_,dim_]:>Apply[Times,Map[Function[mi,
Pair[LorentzIndex[mi[[2]],dim],Momentum[mi[[1]],dim]]
],lpio]];*)
