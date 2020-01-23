pragma Ada_2012;
package body TLSF.Proof.Relation is

   ----------
   -- Find --
   ----------

   function Find
     (Container : V.Sequence; A : Arrow) return Count_Type
   is
   begin
      for Idx in 1..V.Length(Container) loop
         if (V.Get(Container, Idx) = A) then
            return Idx;
         end if;
         pragma Loop_Invariant (not V.Contains(Container, 1, Idx, A));
      end loop;
      return 0;
   end Find;

   -----------------
   -- Find_Second --
   -----------------

   function Find_Second
     (Container : V.Sequence; A : Arrow) return Count_Type
   is
      Len : Count_Type renames V.Length(Container);
      First_Idx : constant Count_Type := Find (Container, A);
   begin
      if Len > 1 and First_Idx in 1 .. Len - 1 then
         for Idx in First_Idx+1..Len loop
            if V.Get(Container, Idx) = A then
               return Idx;
            end if;
         end loop;
      end if;
      return 0;
   end Find_Second;

   function Relate(Container : V.Sequence;
                   From, To  : Element_Type)
                   return V.Sequence
   is
      Len : constant Count_Type := V.Length(Container);
      A : constant Arrow := (From, To);
      Find_Idx : constant Count_Type := Find (Container, A);
   begin
      if Find_Idx > 0 then
         return Container;
      else
         pragma Assert (not V.Contains(Container, 1, Len, A));
         declare
            New_Container : constant V.Sequence := V.Add(Container, A);
            New_Len : constant Count_Type := V.Length(New_Container);
         begin
            pragma Assert (V.Get(New_Container, New_Len) = A);
            return New_Container;
         end;
      end if;
   end Relate;

end TLSF.Proof.Relation;
