with Bits;
with TLSF.Config;
with TLSF.Mem_Block_Size;
use TLSF.Config;
use TLSF.Mem_Block_Size;

private package TLSF.Bitmaps
with SPARK_Mode is

   type First_Level_Index is range SL_Index_Count_Log2 .. FL_Index_Max;
   type Second_Level_Index is range 0 .. SL_Index_Count - 1;

   type Free_List_Status is (Not_Present, Present)
     with Size => 1;

   type First_Level_Map
   is array (First_Level_Index) of Free_List_Status
     with Pack;

   type Second_Level_Map
   is array (Second_Level_Index) of Free_List_Status
     with Pack;

   type Second_Levels_Map is array (First_Level_Index) of Second_Level_Map
     with Pack;

   type Levels_Bitmap is
      record
         First_Level   : First_Level_Map;
         Second_Levels : Second_Levels_Map;
      end record
     with Pack;

   procedure Search_Present
     (bmp : Levels_Bitmap;
      FL  : in out First_Level_Index;
      SL  : in out Second_Level_Index)
     with
       Global => null,
       Depends => (FL =>+ (SL, bmp), SL =>+ (FL, Bmp));

   function Free_Blocks_Present
     (Bmp : Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
      return Boolean
     with Global => null;

   procedure Set_Present
     (bmp : in out Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
     with
       Global => null,
       Depends => (bmp =>+ (FL, SL));

   procedure Set_Not_Present
     (bmp : in out Levels_Bitmap;
      FL  : First_Level_Index;
      SL  : Second_Level_Index)
     with
       Global => null,
       Depends => (bmp =>+ (FL, SL));

   package BM is new Bits (Size);

   subtype Bit_Pos is BM.Bit_Position;

   function Extract_Bits (V : Size; From, To : Bit_Pos) return Size
                          renames BM.Extract;
   function Shift_Right (V : Size; Amount : Bit_Pos) return Size
                         renames BM.Shifts.Logic_Right;
   function Shift_Left (V : Size; Amount : Bit_Pos) return Size
                         renames BM.Shifts.Logic_Left;
   function MSB_Index (V : Size) return Bit_Pos
                       renames BM.Search.Most_Significant_Bit;

   procedure Mapping_Insert(V  : Size;
                            FL : out First_Level_Index;
                            SL : out Second_Level_Index)
     with
       Global => null,
       Depends => ( (FL, SL) => V ),
       Pre => (V >= Shift_Left (1, SL_Index_Count_Log2));

   procedure Mapping_Search (V  : in out Size;
                            FL : out First_Level_Index;
                            SL : out Second_Level_Index);

   procedure Init_Bitmap ( Bmp : out Levels_Bitmap)
     with
       Depends => (Bmp => null),
       Global => null;

end TLSF.Bitmaps;
