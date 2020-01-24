pragma Ada_2012;
package body TLSF.Proof.Relation is

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
