with Ada.Containers;
with TLSF.Proof.Relation;

package body TLSF.Proof.Test.Relation with SPARK_Mode is

   ---------------
   -- Test_Find --
   ---------------

   procedure Test_Find is

      use type Ada.Containers.Count_Type;
      
      type Element is new Natural;
      
      package Relation is new TLSF.Proof.Relation(Element_Type => Element);
      
      R1 : Relation.R;
   begin
      null;
      pragma Assert (Relation.Empty(R1));
      R1 := Relation.Relate(R1, 1,2);
      pragma Assert (Relation.Related(R1,1,2));
      pragma Assert (not Relation.Related(R1,2,3));
      R1 := Relation.Relate(R1, 2,3);
      pragma Assert (Relation.Related(R1,2,3));
   end Test_Find;

   

end TLSF.Proof.Test.Relation;
