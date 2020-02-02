with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers.Formal_Hashed_Sets;
with TLSF.Block.Types;

package body TLSF.Block.Proof with SPARK_Mode is
         
   package body Formal_Model is
      
      ------------------
      -- Find_Address --
      ------------------
      
      function Find_Address
        (V          : Va.Sequence;
         Addr       : Address) return Count_Type
      is
      begin
         for I in 1 .. Va.Length (V) loop
            if Addr = Va.Get (V, I) then
               return I;
            end if;
         end loop;
         return 0;
      end Find_Address;
      
   end Formal_Model;
   

   
   function Block_Present_At_Address(Addr : Valid_Address) return Boolean is
     (Block_Map.Contains(Proof_State.Blocks, Addr));
   
   function Block_At_Address (Addr : Valid_Address) return Block_Header is
     (Block_Map.Element(Proof_State.Blocks, Addr));
   
   function Specific_Block_Present_At_Address
     (Addr  : Valid_Address;
      Block : Block_Header) 
      return Boolean 
   is
     (Block_Present_At_Address(Addr) and then
      Block_At_Address(Addr) = Block);
   
   procedure Put_Block_At_Address
     (Addr  : Valid_Address;
      Block : Block_Header)
   is
      use type Ada.Containers.Count_Type;
      Blocks : Block_Map.Map renames Proof_State.Blocks;
   begin
      -- NB: change Capacity accordingly, if needed
      pragma Assume(Block_Map.Length(Blocks) < Blocks.Capacity);
      Block_Map.Insert(Blocks, Addr, Block);
   end;
   
   procedure Remove_Block_At_Address (Addr : Valid_Address) is
   begin
      Block_Map.Delete(Proof_State.Blocks, Addr);
   end;

   -- Free Lists
   
   function Is_Block_In_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
      return BooleanAll_Blocks_Are_Valid(M)All_Blocks_Are_Valid(M)
   is
      Indices : constant Level_Index := 
                  Calculate_Levels_Indices (Size_Bits(Sz));
      Free_List : Set renames
                    Proof_State.Free_Lists(Indices.First_Level, Indices.Second_Level);
   begin
      return Free_Blocks_Set.Contains (Free_List, Addr);
   end Is_Block_In_Free_List_For_Size;

   function Is_Block_Present_In_Free_Lists
     (Addr : Valid_Address)
      return Boolean
   is
   begin
      for FL_Idx in First_Level_Index'Range loop
         for SL_Idx in Second_Level_Index'Range loop
            if Free_Blocks_Set.Contains(Proof_State.Free_Lists(FL_Idx, SL_Idx), Addr) then
               return True;
            end if;
         end loop;
      end loop;
      return False;
   end Is_Block_Present_In_Free_Lists;
   
   function Is_Block_Present_In_Exactly_One_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
      return Boolean
   is
      Indices : constant Level_Index := 
                  Calculate_Levels_Indices (Size_Bits(Sz));
      Free_List : Set renames
                    Proof_State.Free_Lists(Indices.First_Level, Indices.Second_Level);
   begin
      if not Free_Blocks_Set.Contains (Free_List, Addr) then
         return False;
      end if;
      for FL_Idx in First_Level_Index'Range loop
         for SL_Idx in Second_Level_Index'Range loop
            if FL_Idx /= Indices.First_Level or else
              SL_Idx /= Indices.Second_Level then
               if Free_Blocks_Set.Contains(Proof_State.Free_Lists(FL_Idx, SL_Idx), Addr) then
                  return False;
               end if;
            end if;
         end loop;
      end loop;
      return True;
   end Is_Block_Present_In_Exactly_One_Free_List_For_Size;

   procedure Remove_Block_From_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
   is
      Indices : constant Level_Index :=
                  Calculate_Levels_Indices (Size_Bits(Sz));
   begin
      Free_Blocks_Set.Delete
        (Proof_State.Free_Lists(Indices.First_Level, Indices.Second_Level), Addr);
   end Remove_Block_From_Free_List_For_Size;

   procedure Put_Block_In_Free_List_For_Size
     (Sz   : Size;
      Addr : Valid_Address)
   is
      use type Ada.Containers.Count_Type;   
      
      Indices : constant Level_Index :=
                  Calculate_Levels_Indices (Size_Bits(Sz));
      Free_List : Set renames
                    Proof_State.Free_Lists(Indices.First_Level, Indices.Second_Level);
   begin     
      -- NB: if needed then change Capacity acordingly
      pragma Assume (Free_Blocks_Set.Length(Free_List) < Free_List.Capacity);
      Free_Blocks_Set.Include(Free_List, Addr);
   end Put_Block_In_Free_List_For_Size;

end TLSF.Block.Proof;
