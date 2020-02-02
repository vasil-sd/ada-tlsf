with TLSF.Config;
with TLSF.Mem_Block_Size;
use TLSF.Mem_Block_Size;
use TLSF.Config;
package body TLSF.Bitmaps
with SPARK_Mode is

   procedure Mapping_Insert
     (V  : Size;
      FL : out First_Level_Index;
      SL : out Second_Level_Index)
   is
      First_Bit         : Bit_Pos;
      Second_Level_Bits : Size;
   begin
      First_Bit         := MSB_Index (V);
      pragma Assert (First_Bit >= SL_Index_Count_Log2);
      Second_Level_Bits := Extract_Bits(V,
                                        First_Bit - SL_Index_Count_Log2,
                                        First_Bit - 1);
      FL                := First_Level_Index (First_Bit);
      SL                := Second_Level_Index (Second_Level_Bits);
   end Mapping_Insert;

   procedure Mapping_Search
     (V  : in out Size;
      FL : out First_Level_Index;
      SL : out Second_Level_Index)
   is
      First_Bit : Bit_Pos;
   begin
      First_Bit := MSB_Index (V) - 1;
      V         := V + (2 ** (First_Bit - SL_Index_Count_Log2)) - 1;
      Mapping_Insert (V, FL, SL);
   end Mapping_Search;

   procedure Search_Present
     (bmp : Levels_Bitmap;
      FL : in out First_Level_Index;
      SL : in out Second_Level_Index)
   is
      SL_From   : Second_Level_Index := SL;
      FL_bitmap : First_Level_Map renames bmp.First_Level;
      SL_bitmap : Second_Levels_Map renames bmp.Second_Levels;
   begin
      fl_idx_loop :
      for fl_idx in FL .. First_Level_Index'Last loop
         if FL_bitmap (fl_idx) = Present then
            for sl_idx in SL_From .. Second_Level_Index'Last loop
               if SL_bitmap (fl_idx) (sl_idx) = Present then
                  FL := fl_idx;
                  SL := sl_idx;
                  exit fl_idx_loop;
               end if;
            end loop;
         end if;
         SL_From := Second_Level_Index'First;
      end loop fl_idx_loop;
   end Search_Present;

   procedure Set_Present
     (bmp : in out Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
   is
   begin
      bmp.Second_Levels (FL) (SL) := Present;
      bmp.First_Level (FL) := Present;
   end Set_Present;

   function Second_Levels_Empty
     (Bmp : Levels_Bitmap;
      FL  : First_Level_Index)
      return Boolean
   is
     (for all sl_idx in Second_Level_Index'Range =>
         Bmp.Second_Levels (FL) (sl_idx) = Not_Present);

   procedure Set_Not_Present
     (Bmp : in out Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
   is
   begin
      Bmp.Second_Levels (FL) (SL) := Not_Present;
      Bmp.First_Level (FL) := (if Second_Levels_Empty (Bmp, FL)
                               then  Not_Present
                               else  Present);
   end Set_Not_Present;

   function Free_Blocks_Present
     (Bmp : Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
      return Boolean is
   begin
      return Bmp.Second_Levels(FL) (SL) = Present;
   end Free_Blocks_Present;

   procedure Init_Bitmap ( Bmp : out Levels_Bitmap) is
   begin
      Bmp := Levels_Bitmap'(First_Level   => (others => Not_Present),
                            Second_Levels => (others => (others => Not_Present)));
   end Init_Bitmap;

end TLSF.Bitmaps;
