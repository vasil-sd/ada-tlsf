with TLSF.Proof.Relation;

package body TLSF.Proof.Test.Relation with SPARK_Mode is

   ---------------
   -- Test_Find --
   ---------------

   procedure Test_Find is

      type Element is new Natural;
      
      package Relation is new TLSF.Proof.Relation(Element_Type   => Element);
      
      R1 : Relation.R;
   begin
      null;
      pragma Assert (Relation.Empty(R1));
   end Test_Find;

   

end TLSF.Proof.Test.Relation;
