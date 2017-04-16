Require Export
        FJ.Typing.Wellformedness.WellformedExp
        FJ.Typing.Wellformedness.WellformedDecls.

(* 
   syntax well-formedness 
   ======================
   
   We say that a syntax element is well formed with respect to a 
   class table CT, if any ClassName C, such that C <> Object, we have
   that exists CD, C = get_name CD /\ In CD CT.

   To this we define a simple inductive data types to represent well-formedness.
 *)


