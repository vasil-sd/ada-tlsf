with Ada.Containers.Functional_Vectors;
with TLSF.Proof.Util.Vectors;

package body TLSF.Proof.Test.Util with SPARK_Mode is

   procedure Test_Util is
      subtype Index_Type is Positive;
      subtype Element_Type is Natural;
      
      package V is new Ada.Containers.Functional_Vectors
        (Index_Type, Element_Type);
      
      package U is new TLSF.Proof.Util.Vectors(Element_Type, V);
     
      use type V.Sequence;
      
      T : V.Sequence;
            
   begin
     
      T := V.Add(T, 2);
      
      pragma Assert(U.Find(T, 2) > 0);
      pragma Assert(U.Find_Second(T, 2) = 0);
           
      T := V.Add(T,2);

      pragma Assert(U.Find(T, 2) > 0);
      pragma Assert(U.Find_Second(T, 2) > 0);

      T := V.Add(T, 3);

      pragma Assert(U.Find_Second(T, 2) /= 0);
      
      pragma Assert (U.At_Least_One(T,3));
      pragma Assert (U.At_Most_One(T,3));

      pragma Assert (U.At_Least_One(T,2));
      pragma Assert (U.Find_Second(T, 2) /= 0);
      pragma Assert (not U.At_Most_One(T,2));
      
      pragma Assert (U.Exactly_One(T, 3));
      pragma Assert (not U.Exactly_One(T, 2));
      
      pragma Assert (U.At_Most_One(T, 4));
   end Test_Util;

end TLSF.Proof.Test.Util;
