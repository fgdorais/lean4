// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_shiftr(x_8, x_9);
x_11 = lean_nat_land(x_9, x_8);
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_5);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_9 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
lean_ctor_set(x_2, 0, x_7);
lean_inc(x_6);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_6, x_1, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_9);
lean_inc(x_6);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_6, x_14, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
if (x_8 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_15);
x_22 = l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(x_6, x_21, x_17);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(x_6, x_23, x_25);
lean_dec_ref(x_25);
lean_dec(x_6);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_29);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_30 = x_17;
} else {
 lean_dec_ref(x_17);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(x_6, x_28, x_31);
lean_dec_ref(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_15);
x_38 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(x_6, x_37, x_17);
lean_ctor_set(x_16, 0, x_38);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(x_6, x_39, x_41);
lean_ctor_set(x_16, 0, x_42);
return x_16;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_45);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_46 = x_17;
} else {
 lean_dec_ref(x_17);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(x_6, x_44, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_12);
lean_inc(x_6);
x_53 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_6, x_50, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_54);
if (x_8 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(x_6, x_57, x_60);
lean_dec_ref(x_60);
lean_dec(x_6);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_63);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(x_6, x_65, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_73);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_75 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_75);
lean_dec_ref(x_3);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_71);
lean_inc(x_72);
x_77 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_72, x_1, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_79);
lean_inc(x_72);
x_84 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_72, x_80, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_85);
if (x_74 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc_ref(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34(x_72, x_88, x_91);
lean_dec_ref(x_91);
lean_dec(x_72);
if (lean_is_scalar(x_87)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_87;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_84, 1);
lean_inc_ref(x_94);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_95 = x_84;
} else {
 lean_dec_ref(x_84);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_97);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_98 = x_85;
} else {
 lean_dec_ref(x_85);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_81);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__40_spec__40_spec__48(x_72, x_96, x_99);
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_95;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_94);
return x_101;
}
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_2);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_2, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_3);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_3, 0);
x_106 = lean_ctor_get(x_3, 1);
lean_ctor_set(x_2, 0, x_106);
lean_inc(x_105);
x_107 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_105, x_1, x_2);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_111);
x_112 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_3);
lean_dec_ref(x_3);
lean_ctor_set(x_109, 1, x_112);
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_114);
x_115 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_3);
lean_dec_ref(x_3);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_107, 0, x_116);
return x_107;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_107, 0);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_107);
x_119 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_120);
x_122 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_3);
lean_dec_ref(x_3);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_125 = lean_ctor_get(x_3, 0);
x_126 = lean_ctor_get(x_3, 1);
x_127 = lean_ctor_get(x_3, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_126);
lean_inc(x_125);
x_128 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_125, x_1, x_2);
x_129 = lean_ctor_get(x_128, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_127);
x_136 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_135);
lean_dec_ref(x_135);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
if (lean_is_scalar(x_131)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_131;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_dec(x_2);
x_140 = lean_ctor_get(x_3, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_3, 2);
lean_inc(x_142);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_143 = x_3;
} else {
 lean_dec_ref(x_3);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_139);
lean_inc(x_140);
x_145 = l_Std_Tactic_BVDecide_BVExpr_bitblast(x_140, x_1, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc_ref(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc_ref(x_150);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_151 = x_146;
} else {
 lean_dec_ref(x_146);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_143;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_140);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_142);
x_153 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_152);
lean_dec_ref(x_152);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_148;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_147);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at___Std_Tactic_BVDecide_BVPred_bitblast_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
