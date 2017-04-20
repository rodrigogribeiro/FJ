Require Import
        Arith_base
        List
        FJ.Base
        FJ.Tactics.

(* java specific constants *)

Parameter this : Name.
Parameter Object : Name.     

(* expression syntax *)

Definition ClassName := Name.

Inductive Exp : Set :=
| EVar         : Name -> Exp                        (* variables *)
| EFieldAccess : Exp -> Name -> Exp                 (* field access *)
| EMethodInvoc : Exp -> Name -> list Exp -> Exp     (* method invocation *)
| ECast        : ClassName -> Exp -> Exp            (* cast *)
| ENew         : ClassName -> list Exp -> Exp.      (* object creation *)

(* formal arguments *)

Record FormalArg := mkFormalArg {
   fname : Name ;                  
   ftype : ClassName ;
}.

Instance FormalArgName : Nameable FormalArg :={
   get_name := fname ;
}.

(* field declarations *)

Record Field := mkField {
  fdname : Name ;                   
  fdtype : ClassName ;
}.

Instance FieldDeclName : Nameable Field :={
  get_name := fdname ;                                                
}.
                                                
(* initializers for fields in constructors *)

Record Initializer := mkInitializer {
  ilhs : Name ;                     
  irhs : Name ;
}.
  
(* constructors *)

Record Constructor := mkConstructor {
   kname      : Name ;                    
   kargs      : list FormalArg ;
   ksupers    : list Name ; 
   kinits     : list Initializer ;
}.   

Instance ConstructorName : Nameable Constructor :={
   get_name := kname ;                                                 
}.   

(* methods *)

Record Method := mkMethod {
   mtype  : ClassName ;                   
   mname  : Name ;
   margs  : list FormalArg ;
   mnodup : NoDup (this :: names margs) ;
   mbody  : Exp ;
}.

Instance MethodName : Nameable Method :={
   get_name := mname ;                                       
}.


(* class declarations *)

Record ClassDecl := mkClassDecl {
   cname         : Name ;                  
   cextends      : ClassName ;
   cfields       : list Field ;
   cfieldsnodup  : NoDup cfields ;
   cconstructor  : Constructor ;
   cmethods      : list Method ;
   cmethodsnodup : NoDup cmethods ;
}.        

Instance ClassDeclName : Nameable ClassDecl :={
   get_name := cname ;                                             
}.

(* Programs *)

Definition ClassTable := list ClassDecl.

Record Program := mkProgram {
   pclasses      : ClassTable ;
   pnodupclasses : NoDup pclasses ;                   
   pmain         : Exp ;
}.