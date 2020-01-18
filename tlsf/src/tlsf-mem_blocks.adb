with System.Storage_Elements;
with TLSF.Config;
with TLSF.Bitmaps;
with TLSF.Mem_Block_Size;
use TLSF.Config;
use TLSF.Bitmaps;
use TLSF.Mem_Block_Size;

package body TLSF.Mem_Blocks is

   subtype Free_Block_Header     is Block_Header (Free);
   subtype Occupied_Block_Header is Block_Header (Occupied);

   Block_Header_Size          : constant SSE.Storage_Count :=
                                  Block_Header'Max_Size_In_Storage_Elements;
   Occupied_Block_Header_Size : constant SSE.Storage_Count :=
                                  Occupied_Block_Header'Max_Size_In_Storage_Elements;
   Free_Block_Header_Size     : constant SSE.Storage_Count :=
                                  Free_Block_Header'Max_Size_In_Storage_Elements;

   Aligned_Block_Header_Size          : constant SSE.Storage_Count :=
                                          Align (Block_Header'Max_Size_In_Storage_Elements);
   Aligned_Occupied_Block_Header_Size : constant SSE.Storage_Count :=
                                          Align (Occupied_Block_Header'Max_Size_In_Storage_Elements);
   Aligned_Free_Block_Header_Size     : constant SSE.Storage_Count :=
                                          Align (Free_Block_Header'Max_Size_In_Storage_Elements);

   Small_Block_Size    : constant := 2 ** FL_Index_Shift;

   use type SSE.Storage_Offset;
   use type SSE.Storage_Count;

   pragma Assert (Small_Block_Size >= Block_Header_Size);
   -- should be >= Block_Header max size in storage elements

   function Adjust_And_Align_Size (S : SSE.Storage_Count) return Size is
     (Align (Aligned_Occupied_Block_Header_Size + S));

   function Is_Free_Block_Too_Large (Free_Block : not null access Block_Header;
                                     Block_Size : Size)
                                     return Boolean
   is (Free_Block.Size >= Block_Size + Small_Block_Size);


   procedure Block_Make_Occupied
     (Block : not null access Block_Header)
   is
      Blk : Block_Header with Import, Address => Block.all'Address;
   begin
      Blk := Block_Header'(Status            => Occupied,
                           Prev_Block        => Block.Prev_Block,
                           Prev_Block_Status => Block.Prev_Block_Status,
                           Next_Block_Status => Block.Next_Block_Status,
                           Size              => Block.Size);
   end Block_Make_Occupied;

   procedure Block_Make_Free (Block : not null access Block_Header) is
      BA : Block_Header with Import, Address => Block.all'Address;
      BH : Free_Block_Header := Free_Block_Header'
        (Status            => Free,
         Prev_Block        => Block.Prev_Block,
         Prev_Block_Status => Block.Prev_Block_Status,
         Next_Block_Status => Block.Next_Block_Status,
         Size              => Block.Size,
         Free_List         => Free_Blocks_List'(Prev => null,
                                                Next => null));
--      Blk : Block_Header with Import, Address => Block.all'Address;
   begin
      BA := BH;
        --Blk :=

   end Block_Make_Free;

   function Address_To_Block_Header_Ptr (Addr : System.Address)
                                         return not null access Block_Header
   is
      use type SSE.Storage_Count;
      Block_Addr : System.Address :=
                     (Addr - Aligned_Occupied_Block_Header_Size);
      Block      : aliased Block_Header with Import, Address => Block_Addr;
   begin
      return Block'Unchecked_Access;
   end Address_To_Block_Header_Ptr;

   function Block_Header_Ptr_To_Address (Block : not null access constant Block_Header)
                                         return System.Address
   is
      use type SSE.Storage_Count;
   begin
      return Block.all'Address + Aligned_Occupied_Block_Header_Size;
   end Block_Header_Ptr_To_Address;


   procedure Notify_Neighbors_Of_Block_Status (Block : access Block_Header) is
      Next_Block : access Block_Header := Get_Next_Block (Block);
      Prev_Block : access Block_Header := Get_Prev_Block (Block);
   begin
      if Next_Block /= null then
         Next_Block.Prev_Block_Status := Block.Status;
      end if;
      if Prev_Block /= null then
         Prev_Block.Next_Block_Status := Block.Status;
      end if;
   end Notify_Neighbors_Of_Block_Status;

   function Split_Free_Block (Free_Block : not null access Block_Header;
                              New_Block_Size : Size)
                              return not null access Block_Header
   is
      Remaining_Block_Size : Size := Free_Block.Size - New_Block_Size;
      Remaining_Block : aliased Block_Header
        with
          Import,
          Address => Free_Block.all'Address + New_Block_Size;
   begin
      Block_Make_Free ( Remaining_Block'Access );
      Remaining_Block := Block_Header'
        (Status            => Free,
         Prev_Block        => Free_Block.all'Unchecked_Access,
         Prev_Block_Status => Occupied,
         Next_Block_Status => Free_Block.Next_Block_Status,
         Size              => Remaining_Block_Size,
         Free_List         => Free_Blocks_List'(Prev => null,
                                                Next => null));
      Free_Block.Size              := New_Block_Size;
      Free_Block.Next_Block_Status := Free;
      return Remaining_Block'Unchecked_Access;
   end Split_Free_Block;

   function Insert_To_Free_Blocks_List
     (Block_To_Insert : not null access Block_Header;
      Block_In_List   : access Block_Header)
      return not null access Block_Header is
   begin
      if Block_In_List /= null then
         Block_To_Insert.Free_List.Next := Block_In_List;
         Block_To_Insert.Free_List.Prev := Block_In_List.Free_List.Prev;
         Block_In_List.Free_List.Prev   := Block_To_Insert;
         return Block_In_List.all'Unchecked_Access;
      else
         Block_To_Insert.Free_List :=
           Free_Blocks_List'(Prev => Block_To_Insert.all'Unchecked_Access,
                             Next => Block_To_Insert.all'Unchecked_Access);
         return Block_To_Insert.all'Unchecked_Access;
      end if;
   end Insert_To_Free_Blocks_List;


   function Get_Next_Block ( Block : not null access Block_Header)
                            return access Block_Header
   is
      Next_Block : aliased Block_Header with Import, Address => Block.all'Address + Block.Size;
   begin
      return (if Block.Next_Block_Status /= Absent
              then Next_Block'Unchecked_Access
              else null);
   end Get_Next_Block;

   function Get_Prev_Block ( Block : not null access Block_Header)
                            return access Block_Header is
   begin
      return (if Block.Prev_Block_Status /= Absent
              then Block.Prev_Block
              else null);
   end Get_Prev_Block;

   function Init_First_Free_Block ( Addr : System.Address;
                              Sz   : SSE.Storage_Count)
                             return not null access Block_Header
   is
      Free_Block_Hdr : aliased Block_Header with Import, Address => Addr;
   begin
      Free_Block_Hdr := Block_Header'
        (Status            => Free,
         Prev_Block        => null,
         Prev_Block_Status => Absent,
         Next_Block_Status => Absent,
         Size              => Size(Sz),
         Free_List         => Free_Blocks_List'(Prev => null,
                                                Next => null));
      return Free_Block_Hdr'Unchecked_Access;
   end Init_First_Free_Block;

   function Block_Was_Last_In_Free_List
     (Block : not null access constant Block_Header) return Boolean is
     -- ERROR here
     -- since list is cyclic:
     --   /-------\
     --  A        B
     --  \--------/
     -- when two last items remain A ->next = B and A->prev = B, so as B
     (Block.Free_List.Prev = Block.Free_List.Next);

   function Unlink_Block_From_Free_List
     (Block : not null access Block_Header)
      return access Block_Header is
   begin
      Block.Free_List.Prev.Free_List.Next := Block.Free_List.Next;
      Block.Free_List.Next.Free_List.Prev := Block.Free_List.Prev;
      return (if Block_Was_Last_In_Free_List (Block)
              then null
              else Block.Free_List.Next);
   end Unlink_Block_From_Free_List;

   procedure Merge_Two_Adjacent_Free_Blocks (Block : not null access Block_Header)
   is
      Next_Block : access Block_Header := Get_Next_Block (Block);
   begin
      Block.Next_Block_Status := Next_Block.Next_Block_Status;
      Block.Size              := Block.Size + Next_Block.Size;
   end Merge_Two_Adjacent_Free_Blocks;

   function Is_Block_Free (Block : access Block_Header)
                           return Boolean is
     (Block /= null and then Block.Status = Free);


   function Search_Suitable_Block
     (FL      : First_Level_Index;
      SL      : Second_Level_Index;
      Bmp     : Levels_Bitmap;
      FB_List : Free_Lists)
      return not null access Block_Header
   is
      Block_Hdr : access Block_Header := null;
      SL_From   : Second_Level_Index := SL;
      FL_From   : First_Level_Index  := FL;
   begin
      Search_Present (Bmp, FL_From, SL_From);
      Block_Hdr := FB_List (FL_From, SL_From);
      pragma Assert (Block_Hdr /= null);
      -- run-time exception will be raised if no block found
      return Block_Hdr;
   end Search_Suitable_Block;

   procedure Remove_Free_Block_From_Lists_And_Bitmap
     (Block   : not null access Block_Header;
      FB_List : in out Free_Lists;
      Bmp     : in out Levels_Bitmap)
   is
      FL : First_Level_Index;
      SL : Second_Level_Index;
   begin
      Mapping_Insert (Block.Size, FL, SL);
      FB_List (FL, SL) := Unlink_Block_From_Free_List (Block);
      if FB_List (FL, SL) = null then
         Set_Not_Present (Bmp, FL, SL);
      end if;
   end Remove_Free_Block_From_Lists_And_Bitmap;

   procedure Insert_Free_Block_To_Lists_And_Bitmap
     (Block : not null access Block_Header;
      FB_List : in out Free_Lists;
      Bmp     : in out Levels_Bitmap)
   is
      FL : First_Level_Index;
      SL : Second_Level_Index;
   begin
      Mapping_Insert (Block.Size, FL, SL);
      FB_List (FL, SL) :=
        Insert_To_Free_Blocks_List (Block_To_Insert => Block,
                                    Block_In_List   => FB_List (FL, SL));
      Set_Present (Bmp, FL, SL);
   end Insert_Free_Block_To_Lists_And_Bitmap;

end TLSF.Mem_Blocks;
