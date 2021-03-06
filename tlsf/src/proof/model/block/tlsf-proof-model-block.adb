package body TLSF.Proof.Model.Block with SPARK_Mode is
  
   function Initial_Block (Space : Address_Space)
                           return Block is
      pragma Assert (Space.Last > Space.First);
      Size : BT.Aligned_Size := Space.Last - Space.First;
      B    : Block := (Space.First, BT.Address_Null, Size);
   begin
      pragma Assert (Valid_Block (Space, B));
      pragma Assert (Next_Block_Address(B) = Space.Last);
      return B;
   end Initial_Block;
   
   function Init_Model(Space : Address_Space)
                       return Formal_Model
   is
      B     : Block := Initial_Block (Space);
      Model : Formal_Model;
   begin
      Model.Mem_Region := Space;
      Model.Blocks := Add(Model.Blocks, B);
      return Model;
   end Init_Model;
      
   procedure Addresses_Equality_Implies_Blocks_Equality
     (M : Formal_Model)
   is 
   begin
      pragma Assert (All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (if (for some I in 1 .. Last (M.Blocks) =>
                       (for Some J in 1 .. Last (M.Blocks) =>
                            I /= J and Get (M.Blocks, I).Address = Get (M.Blocks, J).Address))
                     then
                       not All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (for all I in 1 .. Last (M.Blocks) =>
                       (for all J in 1 .. Last (M.Blocks) =>
                            (if Get (M.Blocks, I).Address = Get (M.Blocks, J).Address
                             then I = J and then 
                             Get (M.Blocks, I) = Get (M.Blocks, J))));
   end Addresses_Equality_Implies_Blocks_Equality;

   procedure Addresses_Equality_Implies_Blocks_Equality
     (M           : Formal_Model;
      Left, Right : Block)
   is
   begin
      Addresses_Equality_Implies_Blocks_Equality (M);
      pragma Assert (if Left.Address = Right.Address then Left = Right);
   end Addresses_Equality_Implies_Blocks_Equality;
   
   
   function Is_First_Block(M: Formal_Model; B: Block) return Boolean is
   begin
      if B.Address = M.Mem_Region.First then
         pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (M.Blocks, 1, Last (M.Blocks)));
         pragma Assert (All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
         pragma Assert (for some Blk of M.Blocks => Blk = B);
         pragma Assert (Get (M.Blocks, 1).Address = B.Address);
         pragma Assert (if Get (M.Blocks, 1) /= B then not Valid (M));
         return True;
      end if;
      return False;
   end Is_First_Block;
   
   
   function Is_Last_Block(M: Formal_Model; B: Block) return Boolean is
   begin
      if Next_Block_Address(B) = M.Mem_Region.Last then
         pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (M.Blocks, 1, Last (M.Blocks)));
         pragma Assert (All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
         pragma Assert (for some Blk of M.Blocks => Blk = B);
         pragma Assert (Get (M.Blocks, Last(M.Blocks)) = B);
         pragma Assert (if Get (M.Blocks, Last (M.Blocks)) /= B then not Valid (M));
         return True;
      end if;
      return False;
   end Is_Last_Block;

   function Is_Adjacent_In_Array (BS          : FV_Pkg.Sequence;
                                  Idx         : Index_Type;
                                  Left, Right : Block)
                                  return Boolean
   is (Get (BS, Idx) = Left and Get (BS, Idx + 1) = Right)
     with Global => null,
     Pre => Idx < Last (BS);
   
   procedure Neighbor_Valid_Blocks_Are_Adjacent_In_Array
     (M : Formal_Model; Left, Right : Block)
     with Global => null,
     Pre => Valid (M) and then
     In_Model (M, Left) and then 
     In_Model (M, Right) and then
     Neighbor_Blocks (Left, Right),
     Post => (for some Idx in 1 .. Last (M.Blocks) - 1 => 
                  Is_Adjacent_In_Array (M.Blocks, Idx, Left, Right))
     and then (for all I in 1 .. Last (M.Blocks) - 1 =>
                   (for all J in 1 .. Last (M.Blocks) - 1 =>
                      (if Is_Adjacent_In_Array (M.Blocks, I, Left, Right)
                       and then Is_Adjacent_In_Array (M.Blocks, J, Left, Right)
                           then I = J)))
   is
      Found_Idx : Extended_Index := Extended_Index'First;
   begin
      pragma Assert (Contains (M.Blocks, 1, Last (M.Blocks), Left));
      pragma Assert (Contains (M.Blocks, 1, Last (M.Blocks), Right));
      pragma Assert (Left /= Right);
      pragma Assert (Length (M.Blocks) >= 2);
      pragma Assert (Last (M.Blocks) >= 2);
      pragma Assert (Left.Address < Right.Address);
      pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (All_Block_Addresses_Are_Uniq(M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (if Get (M.Blocks, Last (M.Blocks)) = Left then
                        Right.Address < Left.Address);
      pragma Assert (Get (M.Blocks, Last (M.Blocks)) /= Left);
      for Idx in 1 .. Last (M.Blocks) - 1 loop
         if Get (M.Blocks, Idx ) = Left then
            Found_Idx := Idx;
            pragma Assert (Found_Idx /= Extended_Index'First);
            pragma Assert (Neighbor_Blocks (Left, Get (M.Blocks, Found_Idx + 1)));
            pragma Assert (Get (M.Blocks, Found_Idx + 1) = Right);
            pragma Assert (Is_Adjacent_In_Array (M.Blocks, Found_Idx, Left, Right));
            exit;
         end if;
         pragma Loop_Invariant (not Contains (M.Blocks, 1, Idx, Left));
         pragma Loop_Invariant (Found_Idx = Extended_Index'First);
      end loop;
      pragma Assert (Found_Idx /= Extended_Index'First);
      pragma Assert (if Found_Idx = Extended_Index'First 
                     then not Contains (M.Blocks, 1, Last (M.Blocks), Left));
      pragma Assert (Contains (M.Blocks, 1, Last (M.Blocks), Left));
      pragma Assert (Found_Idx >= 1);
      pragma Assert (Is_Adjacent_In_Array (M.Blocks, Found_Idx, Left, Right));
      pragma Assert (for some Idx in 1 .. Last (M.Blocks) - 1 => 
                       Is_Adjacent_In_Array (M.Blocks, Idx, Left, Right));
      pragma Assert (All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (if not 
                       (for all I in 1 .. Last (M.Blocks) - 1 =>
                            (for all J in 1 .. Last (M.Blocks) - 1 =>
                               (if Is_Adjacent_In_Array (M.Blocks, I, Left, Right)
                                and then Is_Adjacent_In_Array (M.Blocks, J, Left, Right)
                                then I = J)))
                     then (for some I in 1 .. Last (M.Blocks) =>
                         (for some J in 1 .. Last (M.Blocks) => 
                              I /= J
                          and then Is_Adjacent_In_Array (M.Blocks, I, Left, Right)
                          and then Is_Adjacent_In_Array (M.Blocks, J, Left, Right)
                          and then not 
                            (All_Block_Are_Uniq (M.Mem_Region, M.Blocks, 1, Last (M.Blocks))))));
      
   end Neighbor_Valid_Blocks_Are_Adjacent_In_Array;

   
   function Get_Prev(M: Formal_Model; B: Block) return Block
   is
      Prev : Block := Get(M.Blocks, 1);
   begin
      pragma Assert (if Length(M.Blocks) > 0
                     and not Is_First_Block (M, B)
                     and In_Model(M, B)
                     then Last(M.Blocks) >= 2);
      pragma Assert (Last(M.Blocks) >= 2);
      pragma Assert (Valid_Block(M.Mem_Region, Prev));
      pragma Assert (Contains(M.Blocks, 2, Last(M.Blocks), B));
      pragma Assert (for all From in 1..Last(M.Blocks) => 
                       (for all To in 1..From => 
                          (if Partial_Valid(M.Mem_Region, M.Blocks, 1, Last(M.Blocks))
                           then Partial_Valid(M.Mem_Region, M.Blocks, From, To))));
      pragma Assert (for all From in 1..Last(M.Blocks) => 
                       (for all To in 1..From => 
                          (if Partial_Valid(M.Mem_Region, M.Blocks, From, To)
                           then Coverage_Is_Continuous(M.Mem_Region, M.Blocks, From, To))));
      pragma Assert (for all From in 1..Last(M.Blocks)-1 => 
                       (if not Neighbor_Blocks(Get(M.Blocks, From), Get(M.Blocks, From+1))
                        then not Coverage_Is_Continuous(M.Mem_Region, M.Blocks, From, From+1)));
      for Idx in 2..Last(M.Blocks) loop
         pragma Loop_Invariant (Prev = Get(M.Blocks, Idx-1));
         pragma Loop_Invariant (All_Blocks_Are_Valid(M.Mem_Region, M.Blocks, Idx-1, Idx));
         pragma Loop_Invariant (Coverage_Is_Continuous(M.Mem_Region, M.Blocks, Idx-1, Idx));
         pragma Loop_Invariant (Neighbor_Blocks(Get(M.Blocks, Idx-1), Get(M.Blocks, Idx)));
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
      pragma Assert (for all From in 1..Last(M.Blocks) => 
                       (for all To in 1..From => 
                          (if Partial_Valid(M.Mem_Region, M.Blocks, 1, Last(M.Blocks))
                           then Partial_Valid(M.Mem_Region, M.Blocks, From, To))));
      pragma Assert (for all From in 1..Last(M.Blocks) => 
                       (for all To in 1..From => 
                          (if Partial_Valid(M.Mem_Region, M.Blocks, From, To)
                           then Coverage_Is_Continuous(M.Mem_Region, M.Blocks, From, To))));
      pragma Assert (for all From in 1..Last(M.Blocks)-1 => 
                       (if not Neighbor_Blocks(Get(M.Blocks, From), Get(M.Blocks, From+1))
                        then not Coverage_Is_Continuous(M.Mem_Region, M.Blocks, From, From+1)));
      for Idx in 1..Last(M.Blocks)-1 loop
         Next := Get(M.Blocks, Idx+1);
         pragma Loop_Invariant (Valid_Block(M.Mem_Region, Next));
         pragma Loop_Invariant (All_Blocks_Are_Valid(M.Mem_Region, M.Blocks, Idx, Idx+1));
         pragma Loop_Invariant (Neighbor_Blocks(Get(M.Blocks, Idx), Next));
         pragma Loop_Invariant (if Get(M.Blocks, Idx) = B
                                then Neighbor_Blocks(B, Next));
         pragma Loop_Invariant (In_Model(M, Next));
         pragma Loop_Invariant (not Contains (M.Blocks, 1, Idx - 1, B));
         exit when Get(M.Blocks, Idx) = B;
      end loop;
      pragma Assert (if Next = Get(M.Blocks, 1)
                     then not Contains(M.Blocks, 1, Last(M.Blocks)-1, B));
      pragma Assert (Neighbor_Blocks (B, Next));
      return Next;
   end Get_Next;
      
   function Shift_Index (Idx    : Index_Type;
                         Offset : Count_Type'Base)
                         return Index_Type
   is (Index_Type'Val (Index_Type'Pos (Idx) + Offset))
     with
       Global => null,
       Pre => (if Offset < 0 then
                 Index_Type'Pos (Index_Type'Base'First) - Offset <=
                     Index_Type'Pos (Index_Type'First))
       and then (Offset in 
                   Index_Type'Pos (Index_Type'First) - Index_Type'Pos (Idx) ..
                       Index_Type'Pos (Index_Type'Last) - Index_Type'Pos (Idx));
   pragma Annotate (GNATprove, Inline_For_Proof, Shift_Index);
                   
   procedure Range_Shifted_Preserves_Partial_Validity 
     (Old_Space, New_Space   : Address_Space;
      Old_Blocks, New_Blocks : FV_Pkg.Sequence;
      From                   : Index_Type;
      To                     : Extended_Index;
      Offset                 : Count_Type'Base)
     with
       Global => null,
       Pre =>
         Old_Space = New_Space
         and then
            To <= Last (Old_Blocks)
         and then
       (if Offset < 0 then
          Index_Type'Pos (Index_Type'Base'First) - Offset <=
              Index_Type'Pos (Index_Type'First))
       and then
         (if From <= To then
            Offset in
              Index_Type'Pos (Index_Type'First) - Index_Type'Pos (From) ..
          (Index_Type'Pos (Index_Type'First) - 1) + Length (New_Blocks) -
                  Index_Type'Pos (To))
         and then Range_Shifted (Old_Blocks, New_Blocks, From, To, Offset)
     and then Partial_Valid (Old_Space, Old_Blocks, From, To),
     Post =>
       (if From <= To then
          Partial_Valid (New_Space,
            New_Blocks, 
            Shift_Index (From, Offset),
            Shift_Index (To, Offset)))
   is
   begin
      for Idx in From..To loop
         pragma Loop_Invariant
           (Partial_Valid(Old_Space, Old_Blocks, From, Idx));
         pragma Loop_Invariant
           (for all I in From..Idx =>
              Get(Old_Blocks, I) = Get(New_Blocks, Shift_Index(I, Offset)));
         pragma Loop_Invariant (if Idx >= 1 then Shift_Index(Idx, Offset) >= 1);
         pragma Loop_Invariant (if Shift_Index(Idx, Offset) >= 1 then Idx >= 1);
         pragma Loop_Invariant
           (if Idx >= 1 Then
              (for all I in From..Idx-1 =>
                   Get (Old_Blocks, I).Address < Get (Old_Blocks, I + 1).Address
               and then Get (Old_Blocks, I) = Get (New_Blocks, Shift_Index (I, Offset))
               and then Get (Old_Blocks, I + 1) = Get (New_Blocks, Shift_Index (I, Offset + 1))
               and then Get(New_Blocks, Shift_Index(I,Offset)).Address < Get(New_Blocks, Shift_Index(I, Offset+1)).Address));
         pragma Loop_Invariant
           (if Shift_Index (Idx, Offset) >= 1 then
                (for all I in Shift_Index (From, Offset) .. Shift_Index (Idx, Offset)-1 =>
                       Get (New_Blocks, I).Address < Get (New_Blocks, I + 1).Address));
         pragma Assert (All_Blocks_Are_Valid (New_Space, New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (Coverage_Is_Continuous (New_Space, New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (Blocks_Do_Not_Overlap (New_Space, New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (All_Block_Are_Uniq (New_Space, New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (All_Block_Addresses_Are_Uniq (New_Space, New_Blocks, Shift_Index (From, Offset), Shift_Index (Idx, Offset)));
         pragma Assert (Partial_Valid(New_Space, New_Blocks,Shift_Index(From, Offset), Shift_Index(Idx, Offset)));
         null;
      end loop;
   end Range_Shifted_Preserves_Partial_Validity;

   procedure Range_Equal_Preserves_Partial_Validity 
     (Old_Space, New_Space   : Address_Space;
      Old_Blocks, New_Blocks : FV_Pkg.Sequence;
      From                   : Index_Type;
      To                     : Extended_Index)
     with Global => null,
     Pre => To <= Last (Old_Blocks) and then To <= Last (New_Blocks)
     and then Old_Space = New_Space and then
     Range_Equal (Old_Blocks, New_Blocks, From, To) and then     
     Partial_Valid (Old_Space, Old_Blocks, From, To),
     Post => Partial_Valid (New_Space, New_Blocks, From, To)
   is
   begin
      pragma Assert (for all Idx in From .. To =>
                       Get (Old_Blocks, Idx) = Get (New_Blocks, Idx));
      pragma Assert (Partial_Valid (New_Space, New_Blocks, From, To));
      null;
   end Range_Equal_Preserves_Partial_Validity;
   
   procedure Continuous_Coverage_Implies_Non_Overlapping
     (Space : Address_Space;
      Blocks : FV_Pkg.Sequence;
      From   : Index_Type;
      To     : Extended_Index)
     with 
       Global => null,
       Pre => 
         To <= Last (Blocks) and then 
     All_Blocks_Are_Valid (Space, Blocks, From, To) and then
     Coverage_Is_Continuous (Space, Blocks, From, To) and then
     Blocks_Addresses_Are_In_Ascending_Order (Blocks, From, To),
     Post => 
       Blocks_Do_Not_Overlap (Space, Blocks, From, To)
   is
   begin
      
      for T in From .. To loop
         pragma Loop_Invariant
           (for all I in From .. T =>
              (for all J in From .. T =>
                   (if I < J then Get (Blocks, I).Address < Get (Blocks, J).Address)));
 
         pragma Loop_Invariant
           (for all I in From .. T =>
              (for all J in From .. T =>
                   (if I < J then Get (Blocks, I).Address + Get (Blocks, I).Size <= Get (Blocks, J).Address)));
 
      end loop;

      pragma Assert
        (for all I in From .. To =>
           (for all J in From .. To =>
                (if I < J then Get (Blocks, I).Address < Get (Blocks, J).Address)));
 
      pragma Assert
        (for all I in From .. To =>
           (for all J in From .. To =>
                (if I < J then Get (Blocks, I).Address + Get (Blocks, I).Size <= Get (Blocks, J).Address)));

      
      pragma Assert 
        (if not Blocks_Do_Not_Overlap (Space, Blocks, From, To)
         then 
           (for some I in From .. To =>
                (for some J in From .. To =>
                     (I < J and then 
                      Blocks_Overlap (Space,
                        Get (Blocks, I),
                        Get (Blocks, J))
                      and then
                      Get (Blocks, I).Address + Get (Blocks, I).Size > Get (Blocks, J).Address))));
   end Continuous_Coverage_Implies_Non_Overlapping;

   procedure Continuous_Coverage_Implies_Uniqueness
     (Space : Address_Space;
      Blocks : FV_Pkg.Sequence;
      From   : Index_Type;
      To     : Extended_Index)
     with 
       Global => null,
       Pre => 
         To <= Last (Blocks) and then 
     All_Blocks_Are_Valid (Space, Blocks, From, To) and then
     Coverage_Is_Continuous (Space, Blocks, From, To) and then
     Blocks_Addresses_Are_In_Ascending_Order (Blocks, From, To),
     Post => 
       All_Block_Are_Uniq (Space, Blocks, From, To) and then
     All_Block_Addresses_Are_Uniq (Space, Blocks, From, To)
   is
   begin
      
      for T in From .. To loop
         pragma Loop_Invariant
           (for all I in From .. T =>
              (for all J in From .. T =>
                   (if I < J then Get (Blocks, I).Address < Get (Blocks, J).Address)));

         pragma Loop_Invariant
           (for all I in From .. T =>
              (for all J in From .. T =>
                   (if I > J then Get (Blocks, I).Address > Get (Blocks, J).Address)));
  
         pragma Loop_Invariant
           (for all I in From .. T =>
              (for all J in From .. T =>
                   (if I = J then Get (Blocks, I).Address = Get (Blocks, J).Address)));

      end loop;

      pragma Assert
        (for all I in From .. To =>
           (for all J in From .. To =>
                (if I < J then Get (Blocks, I).Address < Get (Blocks, J).Address)));
      
      pragma Assert
        (for all I in From .. To =>
           (for all J in From .. To =>
                (if I > J then Get (Blocks, I).Address > Get (Blocks, J).Address)));
      
      pragma Assert
        (for all I in From .. To =>
           (for all J in From .. To =>
                (if I = J then Get (Blocks, I).Address = Get (Blocks, J).Address)));
      
      pragma Assert 
        (if not All_Block_Are_Uniq (Space, Blocks, From, To)
         then 
           (for some I in From .. To =>
                (for some J in From .. To =>
                     (I < J and then 
                        (Get (Blocks, I).Address =
                             Get (Blocks, J).Address)))));

      pragma Assert 
        (if not All_Block_Addresses_Are_Uniq (Space, Blocks, From, To)
         then 
           (for some I in From .. To =>
                (for some J in From .. To =>
                     (I < J and then 
                        (Get (Blocks, I).Address =
                             Get (Blocks, J).Address)))));
   end Continuous_Coverage_Implies_Uniqueness;

   
   procedure Partial_Validity_Is_Additive 
     ( Space  : Address_Space;
       Blocks : FV_Pkg.Sequence;
       Left_From : Index_Type;
       Left_To   : Extended_Index;
       Right_From : Index_Type;
       Right_To   : Extended_Index)
     with
       Global => null,
       Pre => 
         Left_To <= Last (Blocks) and then
     Right_To <= Last (Blocks) and then
     Left_To <= Right_To and then
     Left_From <= Right_From and then
     Partial_Valid (Space, Blocks, Left_From, Left_To) and then 
     Partial_Valid (Space, Blocks, Right_From, Right_To) and then
     Right_From <= Left_To,
     Post => Partial_Valid (Space, Blocks, Left_From, Right_To)
   is
   begin
       for Idx in Left_From..Right_To loop
         pragma Loop_Invariant
           (if Idx >= 1 Then
              (for all I in Left_From..Idx-1 =>
                   Get (Blocks, I).Address < Get (Blocks, I + 1).Address));
         pragma Assert (All_Blocks_Are_Valid (Space, Blocks, Left_From, Idx));
         pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (Blocks, Left_From, Idx));
         pragma Assert (Coverage_Is_Continuous (Space, Blocks, Left_From, Idx));
         Continuous_Coverage_Implies_Non_Overlapping (Space, Blocks, Left_From, Idx); 
         pragma Assert (Blocks_Do_Not_Overlap (Space, Blocks, Left_From, Idx));
         pragma Assert (All_Block_Are_Uniq (Space, Blocks, Left_From, Idx));
         pragma Assert (Partial_Valid (Space, Blocks, Left_From, Idx));
         null;
      end loop;
   end Partial_Validity_Is_Additive;
      
   procedure Every_Subseq_Of_Partial_Valid_Seq_Is_Partial_Valid
     (Space  : Address_Space;
      Blocks : FV_Pkg.Sequence;
      From   : Index_Type;
      To     : Extended_Index)
     with Global => null,
     Pre => To <= Last (Blocks)
     and then Partial_Valid (Space, Blocks, From, To),
     Post => (for all I in From .. To =>
                (for all J in From .. I =>
                     Partial_Valid (Space, Blocks, J, I)))
   is
   begin
      for I in From .. To loop
         for J in From .. I loop
            pragma Loop_Invariant (Partial_Valid (Space, Blocks, J, I));
         end loop;
      end loop;
      null;
   end Every_Subseq_Of_Partial_Valid_Seq_Is_Partial_Valid;
     
   procedure Increment_Partial_Validity
     (Space : Address_Space;
      Blocks : FV_Pkg.Sequence;
      From   : Index_Type;
      To     : Index_Type)
     with Global => null,
     Pre => To < Last (Blocks)
     and then Partial_Valid (Space, Blocks, From, To)
     and then Valid_Block (Space, Get (Blocks, To + 1))
     and then Valid_Block (Space, Get (Blocks, To))
     and then Neighbor_Blocks (Get (Blocks, To), Get (Blocks, To + 1)),
     Post => Partial_Valid (Space, Blocks, From, To + 1)
   is
   begin
      for Idx in From .. To loop
         pragma Assert (Get (Blocks, Idx).Address < Get (Blocks, Idx + 1).Address);
         pragma Assert (Neighbor_Blocks (Get (Blocks, Idx), Get (Blocks, Idx + 1)));
         pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (Blocks, From, Idx + 1));
         pragma Assert (Coverage_Is_Continuous (Space, Blocks, From, Idx + 1));
         Continuous_Coverage_Implies_Non_Overlapping
           (Space, Blocks, From, Idx + 1);
         pragma Assert (Blocks_Do_Not_Overlap (Space, Blocks, From, Idx + 1));
         Continuous_Coverage_Implies_Uniqueness
           (Space, Blocks, From, Idx + 1);
         pragma Assert (All_Block_Are_Uniq (Space, Blocks, From, Idx + 1));
         pragma Loop_Invariant (Get (Blocks, Idx).Address < Get (Blocks, Idx + 1).Address);
         pragma Loop_Invariant (Neighbor_Blocks (Get (Blocks, Idx), Get (Blocks, Idx + 1)));
         pragma Loop_Invariant (Blocks_Addresses_Are_In_Ascending_Order (Blocks, From, Idx + 1));
         pragma Loop_Invariant (Coverage_Is_Continuous (Space, Blocks, From, Idx + 1));
         pragma Loop_Invariant (Blocks_Do_Not_Overlap (Space, Blocks, From, Idx + 1));
         pragma Loop_Invariant (All_Block_Are_Uniq (Space, Blocks, From, Idx + 1));
         pragma Loop_Invariant (All_Block_Addresses_Are_Uniq (Space, Blocks, From, Idx + 1));
      end loop;
   end Increment_Partial_Validity;
   
   procedure Equality_Preserves_Validity (Old_M, New_M : Formal_Model)
   is
   begin
      pragma Assert (Valid (Old_M));
      pragma Assert (Old_M = New_M);
      pragma Assert (for all Idx in 1 .. Last (Old_M.Blocks) =>
                       Get (Old_M.Blocks, Idx) = Get (New_M.Blocks, Idx));
      pragma Assert (Blocks_Addresses_Are_In_Ascending_Order (New_M.Blocks, 1, Last (New_M.Blocks)));
      pragma Assert (Coverage_Is_Continuous (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
      pragma Assert (Blocks_Do_Not_Overlap (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
      pragma Assert (All_Block_Are_Uniq (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
      pragma Assert (Valid (New_M));
      null;
   end Equality_Preserves_Validity;

   procedure Equality_Preserves_Block_Relations
     (Left_M, Right_M : Formal_Model;
      B               : Block)
   is
   begin
      Equality_Preserves_Validity (Left_M, Right_M);
      pragma Assert (Valid (Right_M));
      pragma Assert (In_Model (Right_M, B));
      pragma Assert (for all Idx in 1 .. Last (Right_M.Blocks) =>
                       Get (Left_M.Blocks, Idx) = Get (Right_M.Blocks, Idx));
      pragma Assert (Is_Last_Block (Left_M, B) = Is_Last_Block (Right_M, B));
      pragma Assert (Is_First_Block (Left_M, B) = Is_First_Block (Right_M, B));
      pragma Assert (if not Is_Last_Block (Left_M, B) then
                        Get_Next (Left_M, B) = Get_Next (Right_M, B));
      pragma Assert (if not Is_First_Block (Left_M, B) then
                        Get_Prev (Left_M, B) = Get_Prev (Right_M, B));
   end Equality_Preserves_Block_Relations; 
   
   procedure All_Blocks_In_Model_Are_Valid (M : Formal_Model)
     with Global => null,
     Pre => Valid (M),
     Post => (for all Idx in 1 .. Last (M.Blocks) =>
                  Valid_Block (M.Mem_Region, Get (M.Blocks, Idx)))
   is 
   begin
      for Idx in 1 .. Last (M.Blocks) loop
         pragma Assert (if not Valid_Block (M.Mem_Region, Get (M.Blocks, Idx)) 
                        and then Valid (M) 
                        then not In_Model (M, Get (M.Blocks, Idx)));
         pragma Loop_Invariant 
           (for all I in 1 .. Idx =>
              Valid_Block (M.Mem_Region, Get (M.Blocks, I)));
      end loop;
   end All_Blocks_In_Model_Are_Valid;

   procedure Continuous_Coverage_Implies_Block_Addresses_In_Ascending_Order
     (AS       : Address_Space;
      BS       : FV_Pkg.Sequence;
      From     : Index_Type;
      To       : Extended_Index)
     with Global => null,
     Pre => To <= Last (BS) and then 
     All_Blocks_Are_Valid (AS, BS, From, To) and then
     Coverage_Is_Continuous (AS, BS, From, To),
     Post => Blocks_Addresses_Are_In_Ascending_Order (BS, From, To)
   is
   begin
      pragma Assert
        (if not Blocks_Addresses_Are_In_Ascending_Order (BS, From, To)
         then 
            To < 1 or else
           (for some Idx in From .. To - 1 =>
                Get (Bs, Idx).Address >= Get (Bs, Idx + 1).Address
            and then 
              not Neighbor_Blocks (Get (Bs, Idx), Get (Bs, Idx + 1))
            and then 
              not Coverage_Is_Continuous (AS, BS, From, To)));
   end Continuous_Coverage_Implies_Block_Addresses_In_Ascending_Order;
   
   procedure Blocks_Validity_And_Continuous_Coverage_Implies_Partial_Validity
     (AS       : Address_Space;
      BS       : FV_Pkg.Sequence;
      From     : Index_Type;
      To       : Extended_Index)
     with Global => null,
     Pre => To <= Last (BS) and then 
     All_Blocks_Are_Valid (AS, BS, From, To) and then
     Coverage_Is_Continuous (AS, BS, From, To),
     Post => Partial_Valid (AS, BS, From, To)
   is
   begin
      Continuous_Coverage_Implies_Block_Addresses_In_Ascending_Order (AS, BS, From, To);
      Continuous_Coverage_Implies_Non_Overlapping (AS, BS, From, To);
      Continuous_Coverage_Implies_Uniqueness (AS, BS, From, To);
   end  Blocks_Validity_And_Continuous_Coverage_Implies_Partial_Validity;
     
   function Is_Sub_Block (M : Formal_Model;
                          Sub, Orig : Block)
                          return Boolean
   is (Sub.Size < Orig.Size and then
       Sub.Address in Orig.Address .. Orig.Address + Orig.Size - 1 and then
       Integer (Sub.Address) + Integer (Sub.Size) in 0 .. Integer (BT.Address'Last) and then
       Sub.Address + Sub.Size in Orig.Address .. Orig.Address + Orig.Size and then
         (if Orig.Prev_Block_Address /= BT.Address_Null then
             Sub.Prev_Block_Address in Orig.Prev_Block_Address .. Sub.Address - 1
               or else Sub.Prev_Block_Address = BT.Address_Null
          else Sub.Prev_Block_Address in Orig.Address .. Sub.Address - 1
          or else Sub.Prev_Block_Address = BT.Address_Null))
     with Global => null,
     Pre => Valid_Block (M.Mem_Region, Orig);
   
   procedure Sub_Block_Of_Valid_Block_Is_Valid
     (M : Formal_Model;
      Sub, Orig : Block)
     with Global => null,
     Pre => Valid_Block (M.Mem_Region, Orig) and then
     Is_Sub_Block (M, Sub, Orig),
     Post => Valid_Block (M.Mem_Region, Sub)
   is
   begin
      pragma Assert (Orig.Address in M.Mem_Region.First .. M.Mem_Region.Last);
      pragma Assert (Orig.Address + Orig.Size in M.Mem_Region.First .. M.Mem_Region.Last);
      pragma Assert (Sub.Address in Orig.Address .. Orig.Address + Orig.Size - 1);
      pragma Assert (Sub.Address in M.Mem_Region.First .. M.Mem_Region.Last);
      pragma Assert (Sub.Address + Sub.Size in Orig.Address .. Orig.Address + Orig.Size);
      pragma Assert (Sub.Address + Sub.Size in M.Mem_Region.First .. M.Mem_Region.Last);
      pragma Assert (if Sub.Prev_Block_Address /= BT.Address_Null
                     then Sub.Prev_Block_Address in M.Mem_Region.First .. M.Mem_Region.Last);
      pragma Assert (Sub.Prev_Block_Address in M.Mem_Region.First .. M.Mem_Region.Last
                    or else Sub.Prev_Block_Address = BT.Address_Null);
      pragma Assert (Valid_Block(M.Mem_Region, Sub));
   end Sub_Block_Of_Valid_Block_Is_Valid;
                              
   
   procedure Split_Block (M               : Formal_Model;
                          B               : Block;
                          L_Size, R_Size  : BT.Aligned_Size;
                          B_Left, B_Right : out Block;
                          New_M           : out Formal_Model)
   is
      Next : Block := B;
      Old_Blocks : FV_Pkg.Sequence;
   begin
      New_M := M;
      
      All_Blocks_In_Model_Are_Valid (M);
      pragma Assert (Valid_Block (M.Mem_Region, B));

      B_Left := Block'(B.Address, B.Prev_Block_Address, L_Size);      
      
      pragma Assert (Is_Sub_Block (New_M, B_Left, B));
      Sub_Block_Of_Valid_Block_Is_Valid (New_M, B_Left, B);                                         

      B_Right := Block'(Next_Block_Address (B_Left), B_Left.Address, R_Size);
      
      pragma Assert (Is_Sub_Block (New_M, B_Right, B));
      Sub_Block_Of_Valid_Block_Is_Valid (New_M, B_Right, B);
      
      pragma Assert (Next_Block_Address (B_Right) = Next_Block_Address (B));
      pragma Assert (Neighbor_Blocks (B_Left, B_Right));
      
      pragma Assert (B_Left /= B and then B_Left.Address = B.Address);
      pragma Assert (In_Model (M, B));
      pragma Assert (if In_Model (M, B_Left) then
                       not Blocks_Addresses_Are_In_Ascending_Order
                         (M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (not In_Model (M, B_Left));
      
      pragma Assert (Blocks_Overlap (M.Mem_Region, B, B_Right));
      pragma Assert (if In_Model (M, B_Right) then
                       not Blocks_Do_Not_Overlap
                         (M.Mem_Region, M.Blocks, 1, Last (M.Blocks)));
      pragma Assert (not In_Model (M, B_Right));
      pragma Assert (In_Model (New_M, B));
      pragma Assert (Valid (New_M));
      Equality_Preserves_Block_Relations(M, New_M, B);
      pragma Assert (if not Is_First_Block (M, B) then
                        Get_Prev (M, B) = Get_Prev (New_M, B));
      pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
      if not Is_Last_Block (M, B) then
         Next := Get_Next(M, B);
         pragma Assert (Neighbor_Blocks (B, Next));
      end if;
      Every_Subseq_Of_Partial_Valid_Seq_Is_Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks));
      Every_Subseq_Of_Partial_Valid_Seq_Is_Partial_Valid (M.Mem_Region, M.Blocks, 1, Last (M.Blocks));
      for Idx in 1 .. Last (New_M.Blocks) loop
         if B = Get (New_M.Blocks, Idx) then
            Equality_Preserves_Block_Relations (M, New_M, B);
            pragma Assert (if not Is_Last_Block (M, B) then Idx < Last (New_M.Blocks));
            pragma Assert (if Idx < Last (New_M.Blocks) then not Is_Last_Block(New_M, B));
            if Idx < Last (New_M.Blocks) then
               pragma Assert (not Is_Last_Block(New_M, B));
               pragma Assert (B = Get (New_M.Blocks, Idx));
               pragma Assert (Neighbor_Blocks (B, Next));
               pragma Assert (Neighbor_Blocks (Get (New_M.Blocks, Idx), Next));
               Neighbor_Valid_Blocks_Are_Adjacent_In_Array (New_M, Get (New_M.Blocks, Idx), Next);
               pragma Assert (Is_Adjacent_In_Array (New_M.Blocks, Idx, Get (New_M.Blocks, Idx), Next));
               pragma Assert (B = Get (New_M.Blocks, Idx));
               pragma Assert (Is_Adjacent_In_Array (M.Blocks, Idx, B, Next));
               pragma Assert (Next = Get (New_M.Blocks, Idx + 1));
            end if;
            pragma Assert (if Idx < Last (New_M.Blocks) then Next = Get (New_M.Blocks, Idx + 1));
            pragma Assert (not Contains (New_M.Blocks, 1, Idx - 1, B));
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx));
            pragma Assert (All_Block_Are_Uniq (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
            pragma Assert (for all I in 1 .. Last (New_M.Blocks) => 
                             (if I /= Idx then 
                                 Get (New_M.Blocks, I) /= B));
            pragma Assert (if Idx > 1 then
                              Neighbor_Blocks
                             ( Get (New_M.Blocks, Idx - 1), B));
            pragma Assert (if Idx < Last (New_M.Blocks)
                           then Next_Block_Address (B) = Get (New_M.Blocks, Idx + 1).Address);
            New_M.Blocks := Set (New_M.Blocks, Idx, B_Left);
            pragma Assert (if Idx < Last (New_M.Blocks) then 
                              Next = Get (New_M.Blocks, Idx + 1));
            pragma Assert (B_Left /= B);
            pragma Assert (Get (New_M.Blocks, Idx) /= B);
            pragma Assert (for all I in 1 .. Last (New_M.Blocks) =>  
                             Get (New_M.Blocks, I) /= B);
            pragma Assert (not Contains (New_M.Blocks, 1, Last (New_M.Blocks), B));
            pragma Assert (Range_Equal (M.Blocks, New_M.Blocks, 1, Idx - 1));
            pragma Assert (if Idx < Last (New_M.Blocks) then
                              Get (New_M.Blocks, Last (New_M.Blocks)) =
                             Get (M.Blocks, Last (M.Blocks))); 
            pragma Assert (if Idx > 1 then Get (New_M.Blocks, 1) = Get (M.Blocks, 1)); 
            Range_Equal_Preserves_Partial_Validity
              (M.Mem_Region, New_M.Mem_Region,
               M.Blocks, New_M.Blocks,
               1, Idx - 1);
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx - 1));
            
            pragma Assert (if Idx > 1 then
                              Neighbor_Blocks
                             (Get (New_M.Blocks, Idx - 1), B));

            pragma Assert (if Idx > 1 then
                              Neighbor_Blocks
                             ( Get (New_M.Blocks, Idx - 1), B_Left));
            pragma Assert (B.Address = B_Left.Address);

            pragma Assert (All_Blocks_Are_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx));
            pragma Assert (Coverage_Is_Continuous (New_M.Mem_Region, New_M.Blocks, 1, Idx));
            Blocks_Validity_And_Continuous_Coverage_Implies_Partial_Validity (New_M.Mem_Region, New_M.Blocks, 1, Idx);
            
            pragma Assume (Idx <= Index_Type'Last - 2);
            pragma Assert (Range_Equal (M.Blocks, New_M.Blocks, Idx + 1, Last (New_M.Blocks)));
            Range_Equal_Preserves_Partial_Validity
              (M.Mem_Region, New_M.Mem_Region,
               M.Blocks, New_M.Blocks,
               Idx + 1, Last (New_M.Blocks));
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 1, Last (New_M.Blocks)));
            
            pragma Assume (Length (New_M.Blocks) < Count_Type'Last);
            Old_Blocks := New_M.Blocks;
            pragma Assert (Get (New_M.Blocks, Idx) = B_Left);
            pragma Assert (Last (Old_Blocks) = Last (New_M.Blocks));
            pragma Assert (Length (Old_Blocks) = Length (New_M.Blocks));
            pragma Assert (Idx in 1 .. Last (New_M.Blocks));
            pragma Assert (Idx in 1 .. Last (Old_Blocks));
            pragma Assert (if Idx < Last (New_M.Blocks)
                           then Next_Block_Address (B) = Get (New_M.Blocks, Idx + 1).Address);
            pragma Assert (if Idx < Last (New_M.Blocks)
                           then Next_Block_Address (B_Right) = Get (New_M.Blocks, Idx + 1).Address);
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 1, Last (New_M.Blocks)));
            New_M.Blocks := Add (New_M.Blocks, Idx + 1, B_Right);
            pragma Assert (if Idx < Last (Old_Blocks) then 
                              Next = Get (New_M.Blocks, Idx + 2));
            pragma Assert (Partial_Valid (New_M.Mem_Region, Old_Blocks, Idx + 1, Last (Old_Blocks)));
            pragma Assert (if Idx < Last (Old_Blocks)
                           then Next_Block_Address (B_Right) = Get (New_M.Blocks, Idx + 2).Address);
            pragma Assert (Last (Old_Blocks) + 1 = Last (New_M.Blocks));
            pragma Assert (Get (New_M.Blocks, Idx) = B_Left);
            
            pragma Assert (if Idx < Last (Old_Blocks) then
                              Get (New_M.Blocks, Last (New_M.Blocks)) =
                             Get (M.Blocks, Last (M.Blocks))); 

            pragma Assert (Range_Equal (Old_Blocks, New_M.Blocks, 1, Idx));
            pragma Assert (Range_Shifted (Old_Blocks, New_M.Blocks, Idx + 1, Last (Old_Blocks), 1));
                             
            Range_Equal_Preserves_Partial_Validity
              (New_M.Mem_Region, New_M.Mem_Region,
               Old_Blocks, New_M.Blocks,
               1, Idx);

            Range_Shifted_Preserves_Partial_Validity
              (New_M.Mem_Region, New_M.Mem_Region,
               Old_Blocks, New_M.Blocks,
               Idx + 1, Last (Old_Blocks), 1);
            
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx));
            pragma Assert (Last (New_M.Blocks) = Last (Old_Blocks) + 1);
            pragma Assert (All_Blocks_Are_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 2, Last (New_M.Blocks)));
            pragma Assert (Coverage_Is_Continuous (New_M.Mem_Region, New_M.Blocks, Idx + 2, Last (New_M.Blocks)));
            Blocks_Validity_And_Continuous_Coverage_Implies_Partial_Validity
              (New_M.Mem_Region, New_M.Blocks, Idx + 2, Last (New_M.Blocks));
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 2, Last (New_M.Blocks)));
            
            pragma Assert (Get (New_M.Blocks, Idx + 1) = B_Right);
            pragma Assert (Get (New_M.Blocks, Idx) = B_Left);
            pragma Assert (Neighbor_Blocks (Get (New_M.Blocks, Idx), Get (New_M.Blocks, Idx + 1)));
            Increment_Partial_Validity (New_M.Mem_Region, New_M.Blocks, 1, Idx);
            pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx + 1));
            if Idx = Last (Old_Blocks) then
               pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
               pragma Assert (B_Right.Address + B_Right.Size = B.Address + B.Size);
               pragma Assert (Boundary_Blocks_Coverage_Is_Correct (M.Mem_Region, M.Blocks));
               pragma Assert (Get (M.Blocks, Last (M.Blocks)) = B);
               pragma Assert (B.Address + B.Size = New_M.Mem_Region.Last);
               pragma Assert (Get (New_M.Blocks, 1).Address = Get (M.Blocks, 1).Address);
               pragma Assert (Boundary_Blocks_Coverage_Is_Correct (New_M.Mem_Region, New_M.Blocks));
               pragma Assert (Valid (New_M));
               pragma Assert (In_Model (New_M, B_Right));
               pragma Assert (In_Model (New_M, B_Left));
               pragma Assert (not In_Model (New_M, B));
               null;
            else
               pragma Assert (Next = Get (New_M.Blocks, Idx + 2));
               pragma Assert (Next_Block_Address (B) = Next.Address);
               pragma Assert (Get (New_M.Blocks, Idx + 1) = B_Right);
               pragma Assert (Next_Block_Address (B_Right) = Next.Address);
               pragma Assert (Next.Address > B_Right.Address);
               Next.Prev_Block_Address := B_Right.Address;
               if Idx + 2 = Last (New_M.Blocks) then

                  pragma Assert (Next.Address =
                                   Get (M.Blocks, Last (M.Blocks)).Address); 
                  pragma Assert (Next.Size =
                                   Get (M.Blocks, Last (M.Blocks)).Size); 
               else
                  pragma Assert (Next.Address =
                                   Get (M.Blocks, Idx + 2).Address); 
                  pragma Assert (Next.Size =
                                   Get (M.Blocks, Idx + 2).Size);                   
               end if;
               
               pragma Assert (Last (Old_Blocks) + 1 = Last (New_M.Blocks));
               
               pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)) =
                                Get (M.Blocks, Last (M.Blocks))); 

               Old_Blocks := New_M.Blocks;
               
               pragma Assert (Get (Old_Blocks, Last (Old_Blocks)) =
                                Get (M.Blocks, Last (M.Blocks))); 

               pragma Assert (Idx + 2 <= Last (New_M.Blocks));
               New_M.Blocks := Set (New_M.Blocks, Idx + 2, Next);
               
               if Idx + 2 = Last (New_M.Blocks) then

                  pragma Assert (Next = Get (New_M.Blocks, Last (New_M.Blocks))); 
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Address =
                                   Get (M.Blocks, Last (M.Blocks)).Address); 
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Size =
                                   Get (M.Blocks, Last (M.Blocks)).Size); 
                  
               else
                  pragma Assert (Idx + 2 < Last (New_M.Blocks));
                  pragma Assert (Range_Equal (Old_Blocks, New_M.Blocks, Idx + 3, Last (New_M.Blocks)));

                  pragma Assert (Get (Old_Blocks, Last (Old_Blocks)) =
                                   Get (M.Blocks, Last (M.Blocks))); 

                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)) =
                                   Get (M.Blocks, Last (M.Blocks))); 
                  
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Address =
                                   Get (M.Blocks, Last (M.Blocks)).Address); 
                  
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Size =
                                   Get (M.Blocks, Last (M.Blocks)).Size); 
                  
               end if;

               pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Address =
                                Get (M.Blocks, Last (M.Blocks)).Address); 
               pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Size =
                                Get (M.Blocks, Last (M.Blocks)).Size); 

               pragma Assert (Range_Equal (Old_Blocks, New_M.Blocks, 1, Idx + 1));

               Range_Equal_Preserves_Partial_Validity
                 (M.Mem_Region, New_M.Mem_Region,
                  Old_Blocks, New_M.Blocks,
                  1, Idx + 1);
               
               if Idx + 2 < Last (New_M.Blocks) then

                  pragma Assert (Range_Equal (Old_Blocks, New_M.Blocks, Idx + 3, Last (New_M.Blocks)));

                  pragma Assert (Partial_Valid (New_M.Mem_Region, Old_Blocks, Idx + 3, Last (New_M.Blocks)));
                  
                  Range_Equal_Preserves_Partial_Validity
                    (M.Mem_Region, New_M.Mem_Region,
                     Old_Blocks, New_M.Blocks,
                     Idx + 3, Last (New_M.Blocks));
               
                  pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 3, Last (New_M.Blocks)));

               end if;
                              
               pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx + 1));
               
               pragma Assert (Neighbor_Blocks (B_Right, Get (New_M.Blocks, Idx + 2)));

               Increment_Partial_Validity (New_M.Mem_Region, New_M.Blocks, 1, Idx + 1);
               pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx + 2));
               
               if Idx + 2 < Last (New_M.Blocks) then
               
                  pragma Assert (Neighbor_Blocks (Get (New_M.Blocks, Idx + 2), Get (New_M.Blocks, Idx + 3)));
                  Increment_Partial_Validity (New_M.Mem_Region, New_M.Blocks, 1, Idx + 2);
                  pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx + 3));

                  pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, Idx + 3, Last (New_M.Blocks)));
                  Partial_Validity_Is_Additive (New_M.Mem_Region, New_M.Blocks, 1, Idx + 3, Idx + 3, Last (New_M.Blocks));

                  pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
               else
                  pragma Assert (Idx + 2 = Last (New_M.Blocks));
                  pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
               end if;

               pragma Assert (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
               
               if Idx = 1 then
                  pragma Assert (B_Left.Address = B.Address);
                  pragma Assert (B_Left.Prev_Block_Address = B.Prev_Block_Address);
                  pragma Assert (B_Left.Prev_Block_Address = BT.Address_Null);
                  pragma Assert (Get (New_M.Blocks, 1) = B_Left);
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Address =
                                   Get (M.Blocks, Last (M.Blocks)).Address); 
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Size =
                                   Get (M.Blocks, Last (M.Blocks)).Size);
                  
                  pragma Assert (Get (New_M.Blocks, 1).Address = New_M.Mem_Region.First);
                  pragma Assert (Next_Block_Address (Get (New_M.Blocks, Last (New_M.Blocks))) = 
                                   New_M.Mem_Region.Last);
                  pragma Assert (Boundary_Blocks_Coverage_Is_Correct (New_M.Mem_Region, New_M.Blocks));
                  pragma Assert (Valid (New_M));
                  pragma Assert (In_Model (New_M, B_Right));
                  pragma Assert (In_Model (New_M, B_Left));
                  pragma Assert (not In_Model (New_M, B));
                  null;
               else
                  pragma Assert (Get (New_M.Blocks, 1) = Get (M.Blocks, 1));
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Address =
                                   Get (M.Blocks, Last (M.Blocks)).Address); 
                  pragma Assert (Get (New_M.Blocks, Last (New_M.Blocks)).Size =
                                   Get (M.Blocks, Last (M.Blocks)).Size); 
                  pragma Assert (Get (New_M.Blocks, 1).Address = New_M.Mem_Region.First);
                  pragma Assert (Get (New_M.Blocks, 1).Prev_Block_Address = BT.Address_Null);
                  pragma Assert (Next_Block_Address (Get (New_M.Blocks, Last (New_M.Blocks))) = 
                                   New_M.Mem_Region.Last);
                  pragma Assert (Boundary_Blocks_Coverage_Is_Correct (New_M.Mem_Region, New_M.Blocks));
                  pragma Assert (Valid (New_M));
                  pragma Assert (In_Model (New_M, B_Right));
                  pragma Assert (In_Model (New_M, B_Left));
                  pragma Assert (not In_Model (New_M, B));
                  null;
               end if;
               null;
            end if;
            pragma Assert (Valid (New_M));
            pragma Assert (In_Model (New_M, B_Left));
            pragma Assert (In_Model (New_M, B_Right));
            exit;
         end if;
         pragma Loop_Invariant (if not Is_Last_Block (M, B) then 
                                   Next = Get_Next (M, B));
         pragma Loop_Invariant (Idx in 1 .. Last (New_M.Blocks));
         pragma Loop_Invariant (not Contains (New_M.Blocks, 1, Idx, B));
         pragma Loop_Invariant (for all I in 1 .. Last (New_M.Blocks) => 
                                  (Get (New_M.Blocks, I) = Get (M.Blocks, I)));
         pragma Loop_Invariant (if not Is_Last_Block (M, B) then
                                   Next = Get_Next (New_M, B));
         pragma Loop_Invariant (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Last (New_M.Blocks)));
         pragma Loop_Invariant (Range_Equal (M.Blocks, New_M.Blocks, 1, Idx));
         pragma Loop_Invariant (Partial_Valid (New_M.Mem_Region, New_M.Blocks, 1, Idx));
      end loop;
      pragma Assert (not In_Model (New_M, B));
      pragma Assert (Valid (New_M));
   end Split_Block;

   function Find_Block (M : Formal_Model; B : Block)
                        return Index_Type
     with Global => null,
     Depends => (Find_Block'Result => (M, B)),
     Pre => Valid (M) and then In_Model (M, B),
     Post =>
       Find_Block'Result in Index_Type'First .. Last (M.Blocks) and then 
       Get (M.Blocks, Find_Block'Result) = B
   is
      Result : Index_Type := 1;
   begin
      pragma Assert (Contains (M.Blocks, 1, Last (M.Blocks), B));
      for Idx in 1 .. Last (M.Blocks) loop
         Result := Idx;
         exit when Get (M.Blocks, Result) = B;
         pragma Loop_Invariant (not Contains (M.Blocks, 1, Idx, B));
      end loop;
      pragma Assert (if Get (M.Blocks, Result) /= B
                     then not (Contains (M.Blocks, 1, Last (M.Blocks), B)));
      return Result;
   end Find_Block;
   
   procedure Join (M           : Formal_Model;
                   Left, Right : Block;
                   B           : out Block;
                   New_M       : out Formal_Model)
   is
      Idx : Index_Type := 1;
   begin
      New_M := M;
      Equality_Preserves_Validity (M, New_M);
      Equality_Preserves_Block_Relations(M, New_M, Left);
      Equality_Preserves_Block_Relations(M, New_M, Right);
      B := Block'(Address            => Left.Address,
                  Prev_Block_Address => Left.Prev_Block_Address,
                  Size               => Left.Size + Right.Size);
      pragma Assert (Valid_Block (M.Mem_Region, Left));
      pragma Assert (Valid_Block (M.Mem_Region, Right));
      pragma Assert (Next_Block_Address (Right) = Next_Block_Address (B));
      pragma Assert (Valid_Block (New_M.Mem_Region, B));
      Idx := Find_Block (M, Left);
      pragma Assert (Get (M.Blocks, Idx) = Left);
      Neighbor_Valid_Blocks_Are_Adjacent_In_Array (M, Left, Right);
      pragma Assert (Is_Adjacent_In_Array(M.Blocks, Idx, Left, Right));
      pragma Assert (Get (M.Blocks, Idx + 1) = Right);
   end Join;
   
end TLSF.Proof.Model.Block;
