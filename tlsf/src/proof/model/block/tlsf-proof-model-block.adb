package body TLSF.Proof.Model.Block with SPARK_Mode is

   function Valid(M : Formal_Model) return Boolean
   is
   begin
      for Idx in 1..Last(M.Blocks) loop
         if not Valid_Block(M, Get(M.Blocks, Idx)) then
            return False;
         end if;
         pragma Assert (Integer(Get(M.Blocks, Idx).Address) + Integer(Get(M.Blocks, Idx).Size) in 0..Integer(BT.Address'Last));
         pragma Loop_Invariant (for all I in 1..Idx => Valid_Block(M, Get(M.Blocks, I)));
      end loop;
      if Last(M.Blocks) >=1 then
         if Get(M.Blocks, 1).Address /= M.First_Address
           or else Next_Block_Address(Get(M.Blocks, Last(M.Blocks))) /= M.Last_Address
         then
            return False;
         end if;
      end if;
      if Last(M.Blocks) > 1 then
         for Idx in 1 .. Last(M.Blocks)-1 loop
            if not Neighbor_Blocks(Get(M.Blocks, Idx), Get(M.Blocks, Idx + 1)) then
               return False;
            end if;
            pragma Loop_Invariant
              (for all I in 1 .. Idx 
               => Neighbor_Blocks(Get(M.Blocks, I), Get(M.Blocks, I + 1)));
         end loop;        
      end if;
      return True;
   end Valid;

   function In_Model(M : Formal_Model; B : Block) return Boolean
   is
   begin
      return Contains(M.Blocks, 1, Last(M.Blocks), B);
   end In_Model;
   
   function Init_Model(First_Address: BT.Aligned_Address;
                       Size         : BT.Aligned_Size)
                       return Formal_Model
   is
      Model : Formal_Model;
      B     : Block := (Address => First_Address, Size => Size);
   begin
      Model.First_Address := First_Address;
      pragma Assert (Integer(First_Address) + Integer(Size) in 0 .. Integer(BT.Address'Last));
      pragma Assert (First_Address + Size > First_Address);
      Model.Last_Address := First_Address + Size;
      --Model := Formal_Model'(Model.Blocks, First_Address, First_Address + Size);
      pragma Assert (B.Address in Model.First_Address..Model.Last_Address);
      pragma Assert (Integer(B.Address) + Integer(B.Size) in 0..Integer(BT.Address'Last));
      pragma Assert (B.Address + B.Size in Model.First_Address..Model.Last_Address);
      pragma Assert(Valid_Block(Model, B));
      Model.Blocks := Add(Model.Blocks, B);
      pragma Assert (Valid_Block(Model, Get(Model.Blocks,1)));
      return Model;
   end Init_Model;
   
   function Is_First_Block(M: Formal_Model; B: Block) return Boolean is
   begin
      if Length(M.Blocks) > 0 and then Get(M.Blocks, 1) = B then
         return True;
      end if;
      return False;
   end Is_First_Block;
   
   
   function Is_Last_Block(M: Formal_Model; B: Block) return Boolean is
   begin
      if Length(M.Blocks) > 0 and then Get(M.Blocks, Last(M.Blocks)) = B then
         return True;
      end if;
      return False;
   end Is_Last_Block;
   
   function Get_Prev(M: Formal_Model; B: Block) return Block
   is
      Prev : Block := Get(M.Blocks, 1);
   begin
      pragma Assert (if Length(M.Blocks) > 0
                     and not Is_First_Block(M, B)
                     and In_Model(M, B)
                     then Last(M.Blocks) >= 2);
      pragma Assert (Last(M.Blocks) >= 2);
      pragma Assert (Valid_Block(M, Prev));
      pragma Assert (Contains(M.Blocks, 2, Last(M.Blocks), B));
      for Idx in 2..Last(M.Blocks) loop
         pragma Loop_Invariant (Valid_Block(M, Prev));
         pragma Loop_Invariant (Valid_Block(M, Get(M.Blocks, Idx)));
         pragma Loop_Invariant (Neighbor_Blocks(Prev, Get(M.Blocks, Idx)));
         pragma Loop_Invariant (if Get(M.Blocks, Idx) = B
                                then Neighbor_Blocks(Prev, B));
         pragma Loop_Invariant (not Contains(M.Blocks, 2, Idx-1, B));
         pragma Loop_Invariant (In_Model(M, Prev));
         exit when Get(M.Blocks, Idx) = B;
         Prev := Get(M.Blocks, Idx);
         pragma Assert (In_Model(M, Prev));
      end loop;
      pragma Assert (if Get(M.Blocks, Last(M.Blocks)) = Prev
                     then not Contains(M.Blocks, 2, Last(M.Blocks), B));
      pragma Assert (Neighbor_Blocks(Prev, B));
      return Prev;
   end Get_Prev;
   
   function Get_Next(M: Formal_Model; B: Block) return Block
   is
      pragma Assert (if Length(M.Blocks) > 0
                     and not Is_First_Block(M, B)
                     and In_Model(M, B)
                     then Last(M.Blocks) >= 2);
      pragma Assert (Last(M.Blocks) >= 2);
      Next : Block := Get(M.Blocks, 1);
   begin
      pragma Assert (Contains(M.Blocks, 1, Last(M.Blocks)-1, B));
      for Idx in 1..Last(M.Blocks)-1 loop
         Next := Get(M.Blocks, Idx+1);
         pragma Loop_Invariant (Valid_Block(M, Next));
         pragma Loop_Invariant (Neighbor_Blocks(Get(M.Blocks, Idx), Next));
         pragma Loop_Invariant (if Get(M.Blocks, Idx) = B
                                then Neighbor_Blocks(B, Next));
         pragma Loop_Invariant (In_Model(M, Next));
         pragma Loop_Invariant (not Contains(M.Blocks, 1, Idx-1, B));
         exit when Get(M.Blocks, Idx) = B;
      end loop;
      pragma Assert (if Next = Get(M.Blocks, 1)
                     then not Contains(M.Blocks, 1, Last(M.Blocks)-1, B));
      pragma Assert(Neighbor_Blocks(B, Next));
      return Next;
   end Get_Next;
   
end TLSF.Proof.Model.Block;
