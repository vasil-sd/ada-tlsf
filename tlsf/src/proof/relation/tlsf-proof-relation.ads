with Ada.Containers.Functional_Sets;

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
     
   package S is new Ada.Containers.Functional_Sets
     (Element_Type => Arrow);
   
   use S;
   
   subtype R is S.Set;
   
   function "="  (Left  : R; Right : R) return Boolean renames S."=";
   function "<=" (Left  : R; Right : R) return Boolean renames S."<=";
   function "<"  (Left  : R; Right : R) return Boolean 
     is (Left <= Right and not (Left = Right));

   function Empty (Rel : R) return Boolean
   is (Length(Rel) = 0);
   
   function Relate(Container : R;
                   From, To  : Element_Type) return R
     with 
       Pre => Length (Container) < Positive_Count_Type'Last,
     Post => (if Contains(Container, Arrow'(From,To))
                then 
                  Relation."="(Relate'Result, Container)
                    else
                    Length (Relate'Result) = Length (Container) + 1
              and Container < Relate'Result
              and Contains(Container, Arrow'(From, To)));
   
   function Related (Container : R;
                     From, To  : Element_Type)
                     return Boolean
   is (Contains(Container, Arrow'(From, To)));
   
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
