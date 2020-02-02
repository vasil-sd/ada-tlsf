with System.Storage_Elements;
with TLSF.Config;
with TLSF.Bitmaps;
with TLSF.Mem_Blocks;
with TLSF.Mem_Block_Size;
-- use TLSF.Config;
use TLSF.Bitmaps;

package body TLSF.Allocator is

   package MBS renames Mem_Block_Size;
   package MB renames Mem_Blocks;

   subtype Blk_Size is MBS.Size;
   use type Blk_Size;

   subtype Free_Lists is MB.Free_Lists;
   subtype Block_Header is MB.Block_Header;

   type Pool_Header is
      record
         Bitmap      : Levels_Bitmap;
         Free_Blocks : Free_Lists;
         Pool_Size   : Blk_Size;
      end record
     with Pack;

   Aligned_Pool_Header_Size : constant SSE.Storage_Count :=
                                MBS.Align (Pool_Header'Max_Size_In_Storage_Elements);

   function Init_Pool (Addr : System.Address;
                       Len  : SSE.Storage_Count)
                       return Pool
   is
      use type SSE.Storage_Count;

      Pool_Addr       : constant System.Address := MBS.Align (Addr);
      Pool_Hdr        : aliased Pool_Header with Import, Address => Pool_Addr;
      Free_Block_Addr : constant System.Address := Pool_Addr + Aligned_Pool_Header_Size;
      Free_Space      : constant SSE.Storage_Count := Len - Aligned_Pool_Header_Size;
      Pool_Size       : constant SSE.Storage_Count := MBS.Align (Free_Space - Config.Align_Size);
      -- Pool_Size is aligned to lower value
      First_Free_Block : access Block_Header;
   begin
      Pool_Hdr.Free_Blocks := (others => (others => null));
      Pool_Hdr.Pool_Size   := Blk_Size (Pool_Size);
      Init_Bitmap (Pool_Hdr.Bitmap);
      First_Free_Block := MB.Init_First_Free_Block (Free_Block_Addr, Pool_Size);
      MB.Insert_Free_Block_To_Lists_And_Bitmap (First_Free_Block, Pool_Hdr.Free_Blocks, Pool_Hdr.Bitmap);
      return Pool'(Pool_Hdr'Unchecked_Access);
   end Init_Pool;

   function Memory_Allocate (Sz   : SSE.Storage_Count;
                             P    : Pool)
                             return System.Address
   is
      FL         : First_Level_Index;
      SL         : Second_Level_Index;
      Free_Block : access Block_Header;
      Block_Size : Blk_Size := MB.Adjust_And_Align_Size (Sz);
   begin
      Mapping_Search (Block_Size, FL, SL);
      Free_Block := MB.Search_Suitable_Block (FL, SL, P.Bitmap, P.Free_Blocks);
      MB.Remove_Free_Block_From_Lists_And_Bitmap (Free_Block, P.Free_Blocks, P.Bitmap);
      MB.Block_Make_Occupied (Free_Block);
      if MB.Is_Free_Block_Too_Large (Free_Block, Block_Size) then
         declare
            Remaining_Block : not null access Block_Header :=
                                MB.Split_Free_Block (Free_Block, Block_Size);
         begin
            MB.Insert_Free_Block_To_Lists_And_Bitmap (Remaining_Block, P.Free_Blocks, P.Bitmap);
         end;
      end if;
      MB.Notify_Neighbors_Of_Block_Status (Free_Block);
      return MB.Block_Header_Ptr_To_Address (Free_Block);
   end Memory_Allocate;

   function Merge_With_Previous_Free (Block   : not null access Block_Header;
                                      FB_List : in out Free_Lists;
                                      Bmp     : in out Levels_Bitmap)
                                      return not null access Block_Header
   is
      Prev_Block : access Block_Header := MB.Get_Prev_Block (Block);
   begin
      if MB.Is_Block_Free (Prev_Block) then
         MB.Remove_Free_Block_From_Lists_And_Bitmap
           (Prev_Block, FB_List, Bmp);
         MB.Merge_Two_Adjacent_Free_Blocks (Prev_Block);
         return Prev_Block;
      end if;
      return Block;
   end Merge_With_Previous_Free;

   function Merge_With_Next_Free (Block   : not null access Block_Header;
                                  FB_List : in out Free_Lists;
                                  Bmp     : in out Levels_Bitmap)
                                  return not null access Block_Header
   is
      Next_Block : access Block_Header := MB.Get_Next_Block (Block);
   begin
      if MB.Is_Block_Free (Next_Block) then
         MB.Remove_Free_Block_From_Lists_And_Bitmap
           (Next_Block, FB_List, Bmp);
         MB.Merge_Two_Adjacent_Free_Blocks (Block);
      end if;
      return Block;
   end Merge_With_Next_Free;

   procedure Memory_Free(Addr : System.Address;
                         P    : Pool)
   is
      Block : access Block_Header := MB.Address_To_Block_Header_Ptr (Addr);
   begin
      MB.Block_Make_Free (Block);
      MB.Notify_Neighbors_Of_Block_Status (Block);
      Block := Merge_With_Previous_Free (Block, P.Free_Blocks, P.Bitmap);
      Block := Merge_With_Next_Free (Block, P.Free_Blocks, P.Bitmap);
      MB.Insert_Free_Block_To_Lists_And_Bitmap (Block, P.Free_Blocks, P.Bitmap);
   end Memory_Free;

end TLSF.Allocator;
