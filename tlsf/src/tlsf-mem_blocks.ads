with System.Storage_Elements;
with TLSF.Config;
with TLSF.Bitmaps;
with TLSF.Mem_Block_Size;
use TLSF.Config;
use TLSF.Bitmaps;
use TLSF.Mem_Block_Size;

private package TLSF.Mem_Blocks is

   type Block_Status is (Free,
                         Occupied,
                         Absent)
     with Size => 2;
   -- Free: block is free
   -- Occupied: block in use
   -- Absent: block is absent (previous of the first
   --         block or next of the last)

   type Block_Header;

   type Block_Header_Access is access all Block_Header;

   type Free_Blocks_List is
      record
         Prev : access Block_Header;
         Next : access Block_Header;
      end record
     with Pack;

   type Block_Header (Status : Block_Status := Free) is
      record
         Prev_Block        : access Block_Header;
         Prev_Block_Status : Block_Status;
         Next_Block_Status : Block_Status;
         Size              : TLSF.Mem_Block_Size.Size;
         case Status is
            when Free   =>
               Free_List : Free_Blocks_List;
            when Occupied |
                 Absent => null;
         end case;
      end record
     with Pack;

   type Unit_Block_Header_Array is array(0..0) of aliased Block_Header;

   type Free_Lists
   is array (First_Level_Index, Second_Level_Index) of access Block_Header;

   procedure Block_Make_Occupied (Block : not null access Block_Header);
   procedure Block_Make_Free (Block : not null access Block_Header);

   function Address_To_Block_Header_Ptr (Addr : System.Address)
                                         return not null access Block_Header;

   function Block_Header_Ptr_To_Address (Block : not null access constant Block_Header)
                                         return System.Address;

   procedure Notify_Neighbors_Of_Block_Status (Block : access Block_Header);

   function Split_Free_Block (Free_Block : not null access Block_Header;
                              New_Block_Size : Size)
                              return not null access Block_Header;

   function Insert_To_Free_Blocks_List
     (Block_To_Insert : not null access Block_Header;
      Block_In_List   : access Block_Header)
      return not null access Block_Header;

   function Get_Next_Block ( Block : not null access Block_Header)
                            return access Block_Header;

   function Get_Prev_Block ( Block : not null access Block_Header)
                            return access Block_Header;

   function Init_First_Free_Block ( Addr : System.Address;
                                    Sz   : SSE.Storage_Count)
                                   return not null access Block_Header;

   function Unlink_Block_From_Free_List (Block : not null access Block_Header)
                                         return access Block_Header
     with Pre => Block.Status = Free;

   procedure Merge_Two_Adjacent_Free_Blocks (Block : not null access Block_Header)
     with Pre => (Block.Status = Free
                  and Block.Next_Block_Status = Free);

   function Is_Block_Free (Block : access Block_Header)
                           return Boolean;

   function Is_Free_Block_Too_Large (Free_Block : not null access Block_Header;
                                     Block_Size : Size)
                                     return Boolean;

   function Adjust_And_Align_Size (S : SSE.Storage_Count) return Size;

   function Search_Suitable_Block (FL      : First_Level_Index;
                                   SL      : Second_Level_Index;
                                   Bmp     : Levels_Bitmap;
                                   FB_List : Free_Lists)
                                   return not null access Block_Header;

   procedure Remove_Free_Block_From_Lists_And_Bitmap (Block   : not null access Block_Header;
                                                      FB_List : in out Free_Lists;
                                                      Bmp     : in out Levels_Bitmap);

   procedure Insert_Free_Block_To_Lists_And_Bitmap (Block : not null access Block_Header;
                                                    FB_List : in out Free_Lists;
                                                    Bmp     : in out Levels_Bitmap);


end TLSF.Mem_Blocks;
