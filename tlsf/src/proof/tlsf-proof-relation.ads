with Ada.Containers.Functional_Vectors;
with TLSF.Proof.Util.Vectors;
generic
   type Element_Type is private;
   with function Elements_Equal(Left, Right : Element_Type)
                                return Boolean is "=";
package TLSF.Proof.Relation with SPARK_Mode is
   
   use Ada.Containers;
   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   
   type Arrow is record
      From : Element_Type;
      To   : Element_Type;
   end record;
   
   function "=" (Left, Right : Arrow) return Boolean
   is (Elements_Equal(Left.From, Right.From)
       and Elements_Equal(Left.To, Right.To));
   
   function Inverse (A : Arrow) return Arrow
   is (Arrow'(From => A.To,
              To   => A.From));
     
   package V is new Ada.Containers.Functional_Vectors
     (Element_Type => Arrow,
      Index_Type   => Positive_Count_Type);
   
   package U is new TLSF.Proof.Util.Vectors(V);
   
   use U;
   
   subtype R is V.Sequence;
   
   function "="
     (Left  : V.Sequence;
      Right : V.Sequence) return Boolean renames V."=";
   
   function "<"
     (Left  : V.Sequence;
      Right : V.Sequence) return Boolean renames V."<";

   function "<="
     (Left  : V.Sequence;
      Right : V.Sequence) return Boolean renames V."<=";

   function Empty (Container : V.Sequence) return Boolean
   is (V.Length(Container) = 0);
   
   function Relate(Container : V.Sequence;
                   From, To  : Element_Type) return V.Sequence
     with 
       Pre => V.Last (Container) < Positive_Count_Type'Last,
     Post => (if Find(Container, Arrow'(From,To)) > 0
                then 
                  Relate'Result = Container
                    else
                      Find(Relate'Result, Arrow'(From, To)) = V.Length(Relate'Result)
              and V.Length (Relate'Result) = V.Length (Container) + 1
              and Container < Relate'Result
              and Arrow'(From, To) = V.Get (Relate'Result, Find(Relate'Result, Arrow'(From, To))));
  
   function Related (Container : V.Sequence;
                     From, To  : Element_Type)
                     return Boolean
   is (Find(Container, Arrow'(From, To)) > 0);
   
--     function Symmetric (Container : V.Sequence) return Boolean
--       with
--         Contract_Cases => 
--           ( (for all Idx in 1..V.Length(Container) =>
--               (not (for all Idx_J in 1..V.Length(Container) => 
--                  (if Idx /= Idx_J
--                     then V.Get(Container, Idx_J) /= V.Get(Container, Idx)))))
--             => Symmetric'Result = True,
--             others
--             => Symmetric'Result = False);
--     
--     function Antysymmetric (Container : V.Sequence) return Boolean
--       with
     
   
--        function Find_Address (V : Va.Sequence; Addr : Address) return Count_Type
--        --  Search for Address
--        with
--          Global => null,
--          Post =>
--              (if Find_Address'Result > 0 then
--                 Find_Address'Result <= Va.Length (V)
--               and Addr = Va.Get (V, Find_Address'Result));
--  
--        function Address_Present(V : Va.Sequence; Addr : Address) return Boolean
--        is (Find_Address(V, Addr) > 0);
      


end TLSF.Proof.Relation;
