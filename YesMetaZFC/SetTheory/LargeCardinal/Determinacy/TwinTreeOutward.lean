import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeSyntax
import YesMetaZFC.Model.Forcing.Order.TreeCertificateSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeRank
import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Truth.ClosedTruth
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.QueryTreeTruth
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.Model.SetTheory.Images.GameCanonicalImage
import YesMetaZFC.Model.Forcing.Collapse.ProductQueryTop
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace

/-! # 双树覆盖反射中原源模型的十二个实际参数

顺序为 ω、字母表列、主条件域、主顺序、值域界、规范实数并名字、
固定收益参数、空顶条件、第一大基数、最小代码及其两个检查名字。
相对公式只量化原载体；成员证书将每个参数实际读为原模型对象。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def qs_source_m (φ : Formula 1 4) : Formula 1 12 :=
  let ω := Term.bound 0; let A := Term.bound 1; let P := Term.bound 2; let V := Term.bound 3
  let W := Term.bound 4; let σ := Term.bound 5; let a := Term.bound 6; let o := Term.bound 7
  let κ := Term.bound 8; let q := Term.bound 9; let sa := Term.bound 10; let sq := Term.bound 11
  .conj (set[12] ⟪
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜A⌝ₛ,⌜ω⌝ₛ,⌜W⌝ₛ) ∧
    ⌜fp_product_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜P⌝ₛ,⌜V⌝ₛ) ∧ ⌜rp_name_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜P⌝ₛ,⌜σ⌝ₛ) ∧
    ⌜bc_binary_m⌝ₚ(⌜ω⌝ₛ,⌜a⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜o⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜o⌝ₛ,⌜κ⌝ₛ,⌜A⌝ₛ) ∧
    ⌜check_m⌝ₚ(⌜o⌝ₛ,⌜a⌝ₛ,⌜sa⌝ₛ) ∧ ⌜check_m⌝ₚ(⌜o⌝ₛ,⌜q⌝ₛ,⌜sq⌝ₛ)⟫)
    (force_at_m (dm_min_m φ) (fun i => [σ,sa,sq].get i) P V P o)

theorem qs_source_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (qs_source_m φ).FreeClosed := by
  simp -implicitDefEqProofs [qs_source_m,Definitional.Formula.FreeClosed]
  exact force_at_closed_l _ _ _ _ _ _ (dm_min_closed_l hc)
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) rfl rfl rfl rfl

structure Qs_source_d (hZF : M.Models ZF) (φ : Formula 1 4) (ρ : Env M 12) : Prop where
  function : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) (ρ.bound 0) (ρ.bound 4)
  product : Fp_product_d hZF (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)
  name : Rp_name_d hZF (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 5)
  binary : Bc_binary_d (ρ.bound 0) (ρ.bound 6)
  empty : ∀ x, ¬ M.mem x (ρ.bound 7)
  alphabet : Entry_d M (ρ.bound 7) (ρ.bound 8) (ρ.bound 1)
  a_check : Check_d M (ρ.bound 7) (ρ.bound 6) (ρ.bound 10)
  q_check : Check_d M (ρ.bound 7) (ρ.bound 9) (ρ.bound 11)
  minimum : Forces_d M (ρ.bound 2) (ρ.bound 3) (ρ.bound 2) (dm_min_m φ)
    (⟨fun i => [ρ.bound 5,ρ.bound 10,ρ.bound 11].get i,ρ.free⟩ : Env M 3) (ρ.bound 7)

theorem qs_source_sat_l (hZF : M.Models ZF) {φ : Formula 1 4} (hc : φ.FreeClosed) (ρ : Env M 12) :
    Formula.satisfies ρ (qs_source_m φ) ↔ Qs_source_d hZF φ ρ := by
  simp only [qs_source_m,Formula.satisfies_conj_iff,Formula.satisfies_isFunctionFromTo_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    fp_product_sat_l hZF,rp_name_sat_l hZF,bc_binary_sat_l hZF.1,Formula.satisfies_isEmpty_iff,
    entry_sat_l M hZF.1,check_sat_l M hZF.1,force_at_sat_l]
  constructor
  · rintro ⟨⟨f,p,n,b,e,a,ca,cq⟩,force⟩
    refine ⟨f,p,n,b,e,a,ca,cq,?_⟩
    exact (forces_env_l hZF.1 _ (dm_min_closed_l hc) _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _).mp force
  · intro h
    refine ⟨⟨h.function,h.product,h.name,h.binary,h.empty,h.alphabet,h.a_check,h.q_check⟩,?_⟩
    exact (forces_env_l hZF.1 _ (dm_min_closed_l hc) _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _).mp h.minimum

def qs_source_parameters_m : Fin 12 → Term 80 := fun i =>
  .bound (([0,5,6,7,8,9,10,11,12,13,14,15] : List (Fin 80)).get i)

def qs_inside_m : Formula 1 80 :=
  .conj (.mem (qs_source_parameters_m 0) (.bound 2)) (.conj (.mem (qs_source_parameters_m 1) (.bound 2))
    (.conj (.mem (qs_source_parameters_m 2) (.bound 2)) (.conj (.mem (qs_source_parameters_m 3) (.bound 2))
    (.conj (.mem (qs_source_parameters_m 4) (.bound 2)) (.conj (.mem (qs_source_parameters_m 5) (.bound 2))
    (.conj (.mem (qs_source_parameters_m 6) (.bound 2)) (.conj (.mem (qs_source_parameters_m 7) (.bound 2))
    (.conj (.mem (qs_source_parameters_m 8) (.bound 2)) (.conj (.mem (qs_source_parameters_m 9) (.bound 2))
    (.conj (.mem (qs_source_parameters_m 10) (.bound 2)) (.mem (qs_source_parameters_m 11) (.bound 2))))))))))))

theorem qs_inside_closed_l : qs_inside_m.FreeClosed := by
  simp -implicitDefEqProofs [qs_inside_m,qs_source_parameters_m,Definitional.Formula.FreeClosed]

theorem qs_inside_sat_l (ρ : Env M 80) :
    Formula.satisfies ρ qs_inside_m ↔ ∀ i, M.mem ((qs_source_parameters_m i).eval ρ) (ρ.bound 2) := by
  simp only [qs_inside_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  rfl

def qs_source_env_l (hZF : M.Models ZF) (ρ : Env M 80)
    (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3))
    (inside : ∀ i, M.mem ((qs_source_parameters_m i).eval ρ) (ρ.bound 2)) :
    Env (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := ρ.bound 3) source.1.2.1) 12 :=
  ⟨fun i => ⟨(qs_source_parameters_m i).eval ρ,inside i⟩,
    fun _ => ⟨(qs_source_parameters_m 0).eval ρ,inside 0⟩⟩

theorem qs_source_decode_l (hZF : M.Models ZF) {φ : Formula 1 4} (hc : φ.FreeClosed) (ρ : Env M 80)
    (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3))
    (trans : M.TransitiveSet (ρ.bound 2)) (inside : ∀ i, M.mem ((qs_source_parameters_m i).eval ρ) (ρ.bound 2))
    (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := ρ.bound 3) source.1.2.1).Models ZF) :
    Formula.satisfies ρ (lr_rel_m (qs_source_m φ) (.bound 2) qs_source_parameters_m) ↔
      Qs_source_d native φ (qs_source_env_l hZF ρ source inside) :=
  (lr_rel_decode_l (kp_pair_l (ZF.modelsKP hZF)) source.1 source.2 trans (qs_source_m φ) (qs_source_closed_l hc)
    (qs_source_env_l hZF ρ source inside) ρ (.bound 2) qs_source_parameters_m rfl (fun _ => rfl)).trans
      (qs_source_sat_l native hc (qs_source_env_l hZF ρ source inside))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 小坍缩双树覆盖的完整有限反射输入

参数槽依次保存原源模型及最小代码（0–15）、小坍缩及正条件（16–19）、
司寇伦树（20–33）、泛型树（34–41）、登记列（42）、联合树（43–53）、
名字树（54–69）、正负子树（70–71）及八个规范检查名字（72–79）。
所有字段均是既有实际证书；原源模型公式经载体相对化读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def qs_cover_parameters_m : Fin 8 → Term 80 := fun i =>
  .bound (([0,0,65,68,70,65,68,71] : List (Fin 80)).get i)

def qs_cover_names_m : Fin 8 → Term 80 := fun i => .bound ⟨i.val + 72,by omega⟩

def qs_input_m (φ : Formula 1 4) : Formula 1 80 :=
  let a : Fin 80 → Term 80 := Term.bound
  .conj (Formula.isOmega (a 0)) (
    .conj (smem_m (𝒞 := kpair_convention_l) (a 1) (a 2) (a 3)) (
    .conj (Formula.isTransitive (a 2)) (
    .conj (v_m kpair_convention_l (a 4) (a 2)) (
    .conj (zc_model_m (a 0) (a 1) (a 2) (a 3)) (
    .conj (qs_inside_m) (
    .conj (lr_rel_m (qs_source_m φ) (a 2) qs_source_parameters_m) (
    .conj (Formula.isUncountableCardinal kpair_convention_l (a 0) (a 12)) (
    .conj (fseq_space_m (𝒞 := kpair_convention_l) (a 0) (a 16) (a 17)) (
    .conj (Formula.subset (a 16) (a 12)) (
    .conj (td_order_m (a 17) (a 18)) (
    .conj (.mem (a 19) (a 17)) (
    .conj (Formula.extensionalNe (a 19) (a 17)) (
    .conj (sh_tree_m (a 0) (a 1) (a 2) (a 3) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30) (a 31) (a 32) (a 33)) (
    .conj (gn_tree_m (a 0) (a 2) (a 6) (a 7) (a 34) (a 35) (a 36) (a 37) (a 38) (a 39) (a 40) (a 41)) (
    .conj (jt_tree_m (a 0) (a 2) (a 6) (a 42) (a 29) (a 35) (a 34) (a 32) (a 33) (a 40) (a 41) (a 30) (a 36) (a 37) (a 38) (a 43) (a 44) (a 45) (a 46) (a 47) (a 48) (a 49) (a 50) (a 51) (a 52) (a 53)) (
    .conj (nr_tree_m (a 0) (a 2) (a 6) (a 7) (a 45) (a 52) (a 53) (a 54) (a 55) (a 56) (a 57) (a 58) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 65) (a 66) (a 67) (a 68) (a 69)) (
    .conj (jt_projection_m (a 46) (a 48) (a 49) (a 30) (a 37) (a 38) (a 54) (a 55)) (
    .conj (qs_tree_m φ true (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 70)) (
    .conj (qs_tree_m φ false (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 71)) (
    .conj (jt_params_m (a 0) (a 2) (a 6) (a 7) (a 42)) (
    td_checks_m (a 19) qs_cover_parameters_m qs_cover_names_m)))))))))))))))))))))

theorem qs_input_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (qs_input_m φ).FreeClosed := by
  have native := lr_rel_closed_l (qs_source_m φ) (qs_source_closed_l hc)
    (.bound 2 : Term 80) qs_source_parameters_m rfl (fun _ => rfl)
  have checks := td_checks_closed_l (.bound 19 : Term 80) qs_cover_parameters_m qs_cover_names_m
    rfl (fun _ => rfl) (fun _ => rfl)
  simp -implicitDefEqProofs [qs_input_m,Definitional.Formula.FreeClosed,Formula.isUncountableCardinal,
    qs_inside_closed_l,native,checks,hc]

structure Qs_cover_data_d (hZF : M.Models ZF) (φ : Formula 1 4) (ρ : Env M 80) : Prop where
  omega : M.IsOmega (ρ.bound 0)
  model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)
  transitive : M.TransitiveSet (ρ.bound 2)
  rank : V_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 4) (ρ.bound 2)
  theory : Zc_model_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)
  inside : ∀ i, M.mem ((qs_source_parameters_m i).eval ρ) (ρ.bound 2)
  source_truth : Formula.satisfies ρ (lr_rel_m (qs_source_m φ) (.bound 2) qs_source_parameters_m)
  large : M.IsUncountableCardinal (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 12)
  collapse : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 16) (ρ.bound 17)
  bound : M.MemberSubset (ρ.bound 16) (ρ.bound 12)
  order : ∀ p q, Entry_d M p q (ρ.bound 18) ↔ M.mem p (ρ.bound 17) ∧ M.mem q (ρ.bound 17) ∧ M.MemberSubset q p
  positive : M.mem (ρ.bound 19) (ρ.bound 17)
  nonzero : ρ.bound 19 ≠ ρ.bound 17
  sh : Sh_tree_d hZF (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 20) (ρ.bound 21) (ρ.bound 22) (ρ.bound 23) (ρ.bound 24) (ρ.bound 25) (ρ.bound 26) (ρ.bound 27) (ρ.bound 28) (ρ.bound 29) (ρ.bound 30) (ρ.bound 31) (ρ.bound 32) (ρ.bound 33)
  gn : Gn_tree_d hZF (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7) (ρ.bound 34) (ρ.bound 35) (ρ.bound 36) (ρ.bound 37) (ρ.bound 38) (ρ.bound 39) (ρ.bound 40) (ρ.bound 41)
  joint : Jt_tree_d hZF (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 42) (ρ.bound 29) (ρ.bound 35) (ρ.bound 34) (ρ.bound 32) (ρ.bound 33) (ρ.bound 40) (ρ.bound 41) (ρ.bound 30) (ρ.bound 36) (ρ.bound 37) (ρ.bound 38) (ρ.bound 43) (ρ.bound 44) (ρ.bound 45) (ρ.bound 46) (ρ.bound 47) (ρ.bound 48) (ρ.bound 49) (ρ.bound 50) (ρ.bound 51) (ρ.bound 52) (ρ.bound 53)
  link : Nr_link_d hZF joint (ρ.bound 7) (ρ.bound 54) (ρ.bound 55) (ρ.bound 56) (ρ.bound 57) (ρ.bound 58) (ρ.bound 59) (ρ.bound 60) (ρ.bound 61) (ρ.bound 62) (ρ.bound 63) (ρ.bound 64) (ρ.bound 65) (ρ.bound 66) (ρ.bound 67) (ρ.bound 68) (ρ.bound 69)
  pos : Qs_tree_d hZF φ true link.tree (ρ.bound 9) (ρ.bound 10) (ρ.bound 70)
  neg : Qs_tree_d hZF φ false link.tree (ρ.bound 9) (ρ.bound 10) (ρ.bound 71)
  params : Jt_params_d (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7) (ρ.bound 42)
  checks : ∀ i, Check_d M (ρ.bound 19) ((qs_cover_parameters_m i).eval ρ) ((qs_cover_names_m i).eval ρ)

theorem qs_input_sat_l (hZF : M.Models ZF) {φ : Formula 1 4} (hc : φ.FreeClosed) (ρ : Env M 80) :
    Formula.satisfies ρ (qs_input_m φ) ↔ Qs_cover_data_d hZF φ ρ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let a : Fin 80 → Term 80 := Term.bound
  simp only [qs_input_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,smem_sat_l I,
    Formula.satisfies_isTransitive_iff,v_sat_l I hZF.1,zc_model_sat_l I hZF.1,qs_inside_sat_l,
    Formula.satisfies_isUncountableCardinal_iff I hZF.1,fseq_space_sat_l I hZF.1,Formula.satisfies_subset_iff,
    td_order_sat_l hZF.1,Formula.satisfies_mem_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,sh_tree_sat_l hZF,gn_tree_sat_l hZF,jt_tree_sat_l hZF,
    nr_tree_sat_l hZF,jt_projection_sat_l hZF,jt_params_sat_l hZF.1,td_checks_sat_l hZF.1]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
    let link : Nr_link_d hZF h15 (ρ.bound 7) (ρ.bound 54) (ρ.bound 55) (ρ.bound 56) (ρ.bound 57) (ρ.bound 58) (ρ.bound 59) (ρ.bound 60) (ρ.bound 61) (ρ.bound 62) (ρ.bound 63) (ρ.bound 64) (ρ.bound 65) (ρ.bound 66) (ρ.bound 67) (ρ.bound 68) (ρ.bound 69) := ⟨h16,h17⟩
    refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,link,?_,?_,h20,h21⟩
    · exact (qs_tree_sat_l hZF hc true ρ (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 70) link.tree).mp h18
    · exact (qs_tree_sat_l hZF hc false ρ (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 71) link.tree).mp h19
  · intro h
    refine ⟨h.omega,h.model,h.transitive,h.rank,h.theory,h.inside,h.source_truth,h.large,h.collapse,h.bound,
      h.order,h.positive,h.nonzero,h.sh,h.gn,h.joint,h.link.tree,h.link.projections,?_,?_,h.params,h.checks⟩
    · exact (qs_tree_sat_l hZF hc true ρ (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 70) h.link.tree).mpr h.pos
    · exact (qs_tree_sat_l hZF hc false ρ (a 2) (a 6) (a 7) (a 9) (a 0) (a 10) (a 65) (a 54) (a 55) (a 59) (a 60) (a 61) (a 62) (a 63) (a 64) (a 66) (a 67) (a 68) (a 69) (a 71) h.link.tree).mpr h.neg

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原题设中的统一小坍缩力迫覆盖

完整有限输入在同一个实际可数模型中反射。先解码原源模型、名字和全部
树证书，再调用已经实现的吸收构枝及截面秩论证，得到每个通过原条件的
小泛型扩张中的覆盖。力迫判据及有限参数反射消去背景可数性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem Qs_cover_data_d.countable_cover_l (hZFC : M.Models ZFC) {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d (ZFC.models_zf_l hZFC) φ ρ)
    (s : Nat → M.Domain) (onto : Function.Surjective s)
    (O : Cond_order_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17))
    {H : M.Domain → Prop} (small : Generic_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) H) :
    ∃ k : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) H).Domain,
      (∀ a, Gval_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) H a (k a)) ∧
      Td_cover_d (kp_pair_l (ZF.modelsKP (preserves_zf_l O (ZFC.models_zf_l hZFC) small)))
        (k (ρ.bound 0)) (k (ρ.bound 0)) (k (ρ.bound 65)) (k (ρ.bound 68)) (k (ρ.bound 70))
        (k (ρ.bound 65)) (k (ρ.bound 68)) (k (ρ.bound 71)) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let N := smdl_structure_l I (R := ρ.bound 3) data.model.1.2.1
  let ν := qs_source_env_l hZF ρ data.model data.inside
  have native := ZFC.models_zf_l (data.theory.native_l I hZF data.omega)
  have seed := (qs_source_decode_l hZF hc ρ data.model data.transitive data.inside native).mp data.source_truth
  -- 显式固定两个赋值，只比较有限槽位，避免展开整个力迫递归。
  let δ : Env N 3 := ⟨fun i => [ν.bound 5,ν.bound 10,ν.bound 11].get i,ν.free⟩
  let δ' : Env N 3 := ⟨fun i => [ν.bound 5,ν.bound 10,ν.bound 11].get i,fun _ => ν.bound 5⟩
  have minimum := (forces_env_l (M := N) (B := ν.bound 2) (R := ν.bound 3) (z := ν.bound 2)
    native.1 (dm_min_m φ) (dm_min_closed_l hc) δ δ' (fun _ => rfl) (ν.bound 7)).mp seed.minimum
  exact qs_collapse_cover_l hZFC data.model data.transitive (ν.bound 0) data.omega data.theory hc data.rank
    seed.function seed.product seed.name seed.binary seed.empty seed.alphabet data.large seed.a_check seed.q_check minimum
    data.sh data.gn data.joint data.link data.pos data.neg data.params data.collapse data.bound O data.order s onto small

theorem Qs_cover_data_d.countable_forces_l (hZFC : M.Models ZFC) {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d (ZFC.models_zf_l hZFC) φ ρ)
    (s : Nat → M.Domain) (onto : Function.Surjective s) :
    Forces_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) td_cover0_m
      ⟨fun i => (qs_cover_names_m i).eval ρ,ρ.free⟩ (ρ.bound 19) := by
  let hZF := ZFC.models_zf_l hZFC
  have O : Cond_order_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) := {
    refl := fun p hp => (data.order p p).mpr ⟨hp,hp,fun _ h => h⟩
    trans := fun p q r hp _ hr pq qr => (data.order p r).mpr
      ⟨hp,hr,fun z hz => ((data.order p q).mp pq).2.2 z (((data.order q r).mp qr).2.2 z hz)⟩
    zero := fun p _ edge => (KP.mem_irrefl_d (ZF.modelsKP hZF) (ρ.bound 17) ((data.order p (ρ.bound 17)).mp edge).2.1).elim }
  apply forces_countable_l O hZF s onto td_cover0_m td_cover0_closed_l _
    (fun i => check_name_l M (check_range_l M hZF) data.positive (data.checks i)) data.positive data.nonzero
  intro H small hp η values
  obtain ⟨k,ground,cover⟩ := data.countable_cover_l hZFC hc ρ s onto O small
  let E := extension_l M hZF (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) H
  let ξ : Env E 8 := ⟨fun i => k ((qs_cover_parameters_m i).eval ρ),fun _ => k (ρ.bound 0)⟩
  have hE := preserves_zf_l O hZF small
  have truth : Formula.satisfies ξ td_cover0_m :=
    (td_cover_sat_l (kp_pair_l (ZF.modelsKP hE)) hE.1 ξ
      (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mpr cover
  have same i : ξ.bound i = η.bound i := (ground ((qs_cover_parameters_m i).eval ρ)).unique_l O hZF small
    ⟨ρ.bound 19,(qs_cover_names_m i).eval ρ,hp,data.checks i,values i⟩
  exact (Formula.closed_env_l _ td_cover0_closed_l (funext same)).mp truth

def qs_cover_force_m : Formula 1 80 :=
  force_at_m td_cover0_m qs_cover_names_m (.bound 17) (.bound 18) (.bound 17) (.bound 19)

theorem qs_cover_force_closed_l : qs_cover_force_m.FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ td_cover0_closed_l (fun _ => rfl) rfl rfl rfl rfl

/-- 给定实际有限证书时，任意背景的原正条件都迫使两棵原树穷尽全部实数。 -/
theorem Qs_cover_data_d.forces_l (hZFC : M.Models ZFC) {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d (ZFC.models_zf_l hZFC) φ ρ) :
    Forces_d M (ρ.bound 17) (ρ.bound 18) (ρ.bound 17) td_cover0_m
      ⟨fun i => (qs_cover_names_m i).eval ρ,ρ.free⟩ (ρ.bound 19) := by
  have valid (N : Structure.{u}) (hN : N.Models ZFC) (s : Nat → N.Domain) (onto : Function.Surjective s)
      (η : Env N 80) (input : Formula.satisfies η (qs_input_m φ)) : Formula.satisfies η qs_cover_force_m := by
    have concrete := (qs_input_sat_l (ZFC.models_zf_l hN) hc η).mp input
    exact (force_at_sat_l td_cover0_m η qs_cover_names_m (.bound 17) (.bound 18) (.bound 17) (.bound 19)).mpr
      (concrete.countable_forces_l hN hc η s onto)
  have truth := FirstOrderSemantics.countable_consequence_l (qs_input_m φ) qs_cover_force_m
    (qs_input_closed_l hc) qs_cover_force_closed_l valid hZFC ρ
    ((qs_input_sat_l (ZFC.models_zf_l hZFC) hc ρ).mpr data)
  exact (force_at_sat_l td_cover0_m ρ qs_cover_names_m (.bound 17) (.bound 18) (.bound 17) (.bound 19)).mp truth

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原双树资料的实际有限输入工厂

前七十二槽保存原模型、乘积、最小代码及树证书；末八槽仅保存实际构造的
检查名字。输入工厂由统一力迫覆盖与最小坏收益排除共同使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 仅组合已有参数，不选择任何对象或名字。 -/
def qs_cover_env_l (v : Fin 72 → M.Domain) (η : Fin 8 → M.Domain) : Env M 80 :=
  ⟨Fin.addCases (m := 72) (n := 8) (motive := fun _ => M.Domain) v η,fun _ => v 19⟩

theorem qs_cover_context_l {φ : Formula 1 4} (hc : φ.FreeClosed) {c X R θ : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (ω : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    {A₀ P V W₀ σ a₀ o κ q₀ sa sq : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω W₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A₀) (hκ : M.IsUncountableCardinal I ω.val κ.val)
    (ca : Check_d (smdl_structure_l I (R := R) source.1.2.1) o a₀ sa)
    (cq : Check_d (smdl_structure_l I (R := R) source.1.2.1) o q₀ sq)
    (minimum : Forces_d (smdl_structure_l I (R := R) source.1.2.1) P V P (dm_min_m φ)
      (⟨fun i => [σ,sa,sq].get i,fun _ => σ⟩ : Env (smdl_structure_l I (R := R) source.1.2.1) 3) o)
    {u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An positive negative : M.Domain}
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (pos : Qs_tree_d hZF φ true link.tree σ.val a₀.val positive)
    (neg : Qs_tree_d hZF φ false link.tree σ.val a₀.val negative)
    (params : Jt_params_d ω.val X P.val V.val C)
    {α Q U p : M.Domain} (collapse : Fseq_space_d I ω.val α Q) (bound : M.MemberSubset α κ.val)
    (order : ∀ r s, Entry_d M r s U ↔ M.mem r Q ∧ M.mem s Q ∧ M.MemberSubset s r)
    (hp : M.mem p Q) (nz : p ≠ Q) :
    ∃ η : Fin 8 → M.Domain, Qs_cover_data_d hZF φ (qs_cover_env_l (fun i => [
    ω.val,c,X,R,θ, -- 原源模型
    A₀.val,P.val,V.val,W₀.val,σ.val,a₀.val,o.val,κ.val,q₀.val,sa.val,sq.val,
    α,Q,U,p, -- 小坍缩及指定正条件
    u,S,L,T,E,K,Wₛ,D,J,Ys,ds,hs,Fs,As, -- 司寇伦树
    Zg,Yg,dg,hg,lg,rg,Fg,Ag,C, -- 泛型树及登记列
    Z,W,Y,a,b,c',d',l,r,F,A, -- 联合树
    de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,positive,negative].get i) η) := by
  obtain ⟨w,cw,_,_⟩ := zf_check_l M hZF hp ω.val
  obtain ⟨y,cy,_,_⟩ := zf_check_l M hZF hp Yn
  obtain ⟨f,cf,_,_⟩ := zf_check_l M hZF hp Fn
  obtain ⟨t,ct,_,_⟩ := zf_check_l M hZF hp positive
  obtain ⟨s,cs,_,_⟩ := zf_check_l M hZF hp negative
  let η : Env M 8 := ⟨fun i => [w,w,y,f,t,y,f,s].get i,fun _ => p⟩
  have checks : ∀ i, Check_d M p ([ω.val,ω.val,Yn,Fn,positive,Yn,Fn,negative].get i) (η.bound i) :=
    Fin.cases cw (Fin.cases cw (Fin.cases cy (Fin.cases cf
      (Fin.cases ct (Fin.cases cy (Fin.cases cf (Fin.cases cs (fun i => Fin.elim0 i))))))))
  let ρ : Env M 80 := qs_cover_env_l (fun i => [
    ω.val,c,X,R,θ, -- 原源模型
    A₀.val,P.val,V.val,W₀.val,σ.val,a₀.val,o.val,κ.val,q₀.val,sa.val,sq.val,
    α,Q,U,p, -- 小坍缩及指定正条件
    u,S,L,T,E,K,Wₛ,D,J,Ys,ds,hs,Fs,As, -- 司寇伦树
    Zg,Yg,dg,hg,lg,rg,Fg,Ag,C, -- 泛型树及登记列
    Z,W,Y,a,b,c',d',l,r,F,A, -- 联合树
    de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,positive,negative].get i) η.bound
  have inside : ∀ i, M.mem ((qs_source_parameters_m i).eval ρ) X :=
    Fin.cases ω.property (Fin.cases A₀.property (Fin.cases P.property (Fin.cases V.property
      (Fin.cases W₀.property (Fin.cases σ.property (Fin.cases a₀.property (Fin.cases o.property
        (Fin.cases κ.property (Fin.cases q₀.property (Fin.cases sa.property (Fin.cases sq.property (fun i => Fin.elim0 i))))))))))))
  let N := smdl_structure_l I (R := R) source.1.2.1
  let ν := qs_source_env_l hZF ρ source inside
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have seed : Qs_source_d native φ ν := by
    refine ⟨fa,product,name,binary,empty,alphabet,ca,cq,?_⟩
    let δ : Env N 3 := ⟨fun i => [σ,sa,sq].get i,fun _ => σ⟩
    let δ' : Env N 3 := ⟨fun i => [ν.bound 5,ν.bound 10,ν.bound 11].get i,ν.free⟩
    exact (forces_env_l (M := N) (B := P) (R := V) (z := P) native.1
      (dm_min_m φ) (dm_min_closed_l hc) δ δ'
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) o).mp minimum
  have parameters : ∀ i, (qs_cover_parameters_m i).eval ρ = ([ω.val,ω.val,Yn,Fn,positive,Yn,Fn,negative].get i) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  have names : ∀ i, (qs_cover_names_m i).eval ρ = η.bound i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  have data : Qs_cover_data_d hZF φ ρ := {
    omega := hw
    model := source
    transitive := trans
    rank := rank
    theory := certificate
    inside := inside
    source_truth := (qs_source_decode_l hZF hc ρ source trans inside native).mpr seed
    large := hκ
    collapse := collapse
    bound := bound
    order := order
    positive := hp
    nonzero := nz
    sh := sh
    gn := gn
    joint := joint
    link := link
    pos := pos
    neg := neg
    params := params
    checks := fun i => by rw [parameters i,names i]; exact checks i }
  exact ⟨η.bound,data⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原树及原最小代码实际装配统一力迫覆盖

八个参数的检查名字由五次规范检查构造产生。原源模型、主乘积、最小代码、
原树的全部证书直接填入有限反射输入；调用方无需另外给出反射或覆盖合同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_force_cover_l {φ : Formula 1 4} (hc : φ.FreeClosed) {c X R θ : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (ω : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    {A₀ P V W₀ σ a₀ o κ q₀ sa sq : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω W₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A₀) (hκ : M.IsUncountableCardinal I ω.val κ.val)
    (ca : Check_d (smdl_structure_l I (R := R) source.1.2.1) o a₀ sa)
    (cq : Check_d (smdl_structure_l I (R := R) source.1.2.1) o q₀ sq)
    (minimum : Forces_d (smdl_structure_l I (R := R) source.1.2.1) P V P (dm_min_m φ)
      (⟨fun i => [σ,sa,sq].get i,fun _ => σ⟩ : Env (smdl_structure_l I (R := R) source.1.2.1) 3) o)
    {u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An positive negative : M.Domain}
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (pos : Qs_tree_d hZF φ true link.tree σ.val a₀.val positive)
    (neg : Qs_tree_d hZF φ false link.tree σ.val a₀.val negative)
    (params : Jt_params_d ω.val X P.val V.val C)
    {α Q U p : M.Domain} (collapse : Fseq_space_d I ω.val α Q) (bound : M.MemberSubset α κ.val)
    (order : ∀ r s, Entry_d M r s U ↔ M.mem r Q ∧ M.mem s Q ∧ M.MemberSubset s r)
    (hp : M.mem p Q) (nz : p ≠ Q) :
    ∃ η : Env M 8, (∀ i, Check_d M p ([ω.val,ω.val,Yn,Fn,positive,Yn,Fn,negative].get i) (η.bound i)) ∧
      Forces_d M Q U Q td_cover0_m η p := by
  obtain ⟨η,data⟩ := qs_cover_context_l hZFC hc source trans rank ω hw certificate
    fa product name binary empty alphabet hκ ca cq minimum sh gn joint link pos neg params collapse bound order hp nz
  let ρ : Env M 80 := qs_cover_env_l (fun i => [
    ω.val,c,X,R,θ, -- 原源模型
    A₀.val,P.val,V.val,W₀.val,σ.val,a₀.val,o.val,κ.val,q₀.val,sa.val,sq.val,
    α,Q,U,p, -- 小坍缩及指定正条件
    u,S,L,T,E,K,Wₛ,D,J,Ys,ds,hs,Fs,As, -- 司寇伦树
    Zg,Yg,dg,hg,lg,rg,Fg,Ag,C, -- 泛型树及登记列
    Z,W,Y,a,b,c',d',l,r,F,A, -- 联合树
    de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,positive,negative].get i) η
  have parameters : ∀ i, (qs_cover_parameters_m i).eval ρ = ([ω.val,ω.val,Yn,Fn,positive,Yn,Fn,negative].get i) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  have names : ∀ i, (qs_cover_names_m i).eval ρ = η i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  let δ : Env M 8 := ⟨η,ρ.free⟩
  have checks : ∀ i, Check_d M p ([ω.val,ω.val,Yn,Fn,positive,Yn,Fn,negative].get i) (δ.bound i) := by
    intro i
    have check := data.checks i
    rw [parameters i,names i] at check
    exact check
  let ξ : Env M 8 := ⟨fun i => (qs_cover_names_m i).eval ρ,ρ.free⟩
  exact ⟨δ,checks,(forces_env_l (B := Q) (R := U) (z := Q) hZF.1 td_cover0_m td_cover0_closed_l ξ δ names p).mp
    (data.forces_l hZFC hc ρ)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原坍缩力迫覆盖得到任意地模型的双树结论

有限参数反射构造实际可数初等子模型及经过指定正条件的泛型滤子；
真值定理给出同一扩张中的覆盖，再把地面覆盖和策略存在性反射回来。
原模型无需外部可数、良基或具有实际泛型滤子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u

private theorem td_reflected_l (N : Structure.{u}) (hZFC : N.Models ZFC) (ρ : Env N 24)
    (O : Cond_order_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13))
    (input : Formula.satisfies ρ td_input_m) (U : N.Domain → Prop)
    (generic : Generic_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) U) (hp : U (ρ.bound 15)) :
    Formula.satisfies ρ td_output_m := by
  let hN := ZFC.models_zf_l hZFC
  obtain ⟨⟨hw, hd, rank, hA, ha, pair, space, tree, pair', space', tree', collapse, order⟩, checks, force⟩ :=
    (td_input_sat_l hN ρ).mp input
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hN generic hp
  let E := extension_l N hN (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) U
  have hE : E.Models ZF := preserves_zf_l O hN generic
  let η : Env N 8 := ⟨fun i => (td_names_m i).eval ρ, fun _ => (td_names_m 0).eval ρ⟩
  let ξ : Env E 8 := ⟨fun i => e ((td_parameters_m i).eval ρ), fun _ => e (ρ.bound 0)⟩
  have values : Env_val_d hN η ξ := by
    intro t
    cases t with
    | bound i => exact hv _ _ (checks i)
    | free _ => exact hv _ _ (checks 0)
  have forced : Forces_d N (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) td_cover0_m η (ρ.bound 15) :=
    (forces_env_l hN.1 td_cover0_m td_cover0_closed_l
      (⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ : Env N 8) η (fun _ => rfl) (ρ.bound 15)).mp force
  have covered := (forcing_truth_l O hN generic td_cover0_m td_cover0_closed_l η ξ values).mp ⟨_, hp, forced⟩
  have cover := (td_cover_sat_l (kp_pair_l (ZF.modelsKP hE)) hE.1 ξ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mp covered
  have result := td_generic_dichotomy_l hZFC hw hd rank hA ha pair space tree pair' space' tree'
    collapse order O generic hp e hi he hv cover
  exact (td_output_sat_l hN ρ).mpr result

variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 任一正坍缩条件迫使两树穷尽已足够；不把泛型存在性列为调用前提。 -/
theorem td_ground_l {ω δ A X a Γ Y F T Λ Z G S C Q p : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d I δ) (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (collapse : Fseq_space_d I ω δ C)
    (order : ∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r)
    (hp : M.mem p C) (hn : p ≠ C) (η : Env M 8)
    (checks : ∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i))
    (force : Forces_d M C Q C td_cover0_m η p) :
    Td_cover_d I ω A Y F T Z G S ∧
      (Tp_win_d hM true true ω A Y F T ∨ Tp_win_d hM false false ω A Z G S) := by
  let O : Cond_order_d M C Q C := {
    refl := fun r hr => (order r r).mpr ⟨hr, hr, fun _ h => h⟩
    trans := fun r s t hr _ ht rs st => (order r t).mpr
      ⟨hr, ht, fun v hv => ((order r s).mp rs).2.2 v (((order s t).mp st).2.2 v hv)⟩
    zero := fun r _ rc => (KP.mem_irrefl_d (ZF.modelsKP hM) C ((order r C).mp rc).2.1).elim }
  let ρ : Env M 24 := ⟨fun i => [ω, δ, A, X, a, Γ, Y, F, T, Λ, Z, G, S, C, Q, p,
    η.bound 0, η.bound 1, η.bound 2, η.bound 3, η.bound 4, η.bound 5, η.bound 6, η.bound 7].get i, η.free⟩
  have names : ∀ i, (td_names_m i).eval ρ = η.bound i := by
    simp only [Fin.forall_fin_succ]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => Fin.elim0 i⟩
  have parameters : ∀ i, (td_parameters_m i).eval ρ = [ω, A, Y, F, T, Z, G, S].get i := by
    simp only [Fin.forall_fin_succ]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => Fin.elim0 i⟩
  have input : Td_input_d hM ρ := by
    refine ⟨⟨hw, hd, rank, hA, ha, pair, space, tree, pair', space', tree', collapse, order⟩,
      fun i => ?_, ?_⟩
    · rw [parameters i, names i]; exact checks i
    · exact (forces_env_l hM.1 td_cover0_m td_cover0_closed_l η
        (⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ : Env M 8) (fun i => (names i).symm) p).mp force
  have result := source_of_generics_theory_l (Γ := ZFC) td_input_m td_output_m td_input_closed_l td_output_closed_l
    (.bound 13) (.bound 14) (.bound 13) (.bound 15) rfl rfl rfl rfl
    (fun N _ hN ρ O input U generic hp => td_reflected_l N hN ρ O input U generic hp)
    hM hZFC ρ O hp hn ((td_input_sat_l hM ρ).mpr input)
  exact (td_output_sat_l hM ρ).mp result

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原正负树的地面覆盖及类型博弈赢家

实际装配的统一小坍缩力迫覆盖直接进入双树地面定理。此处的赢家是两种
类型博弈的二择一；识别同一收益集仍须使用正负声音性及其互斥性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_cover_data_d.ground_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d hZF φ ρ) {V : M.Domain}
    (hd : Woodin_d I (ρ.bound 16)) (rank : V_d I (ρ.bound 16) V) (inside : M.mem (ρ.bound 0) V) :
    Td_cover_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70)
      (ρ.bound 65) (ρ.bound 68) (ρ.bound 71) ∧
      (Tp_win_d hZF true true (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70) ∨
        Tp_win_d hZF false false (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 71)) := by
  let η : Env M 8 := ⟨fun i => (qs_cover_names_m i).eval ρ,ρ.free⟩
  have parameters : ∀ i, (qs_cover_parameters_m i).eval ρ =
      ([ρ.bound 0,ρ.bound 0,ρ.bound 65,ρ.bound 68,ρ.bound 70,ρ.bound 65,ρ.bound 68,ρ.bound 71].get i) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  obtain ⟨a,_,ha⟩ := data.omega.1.1
  exact td_ground_l hZFC data.omega hd rank inside ha data.link.tree.letters.product data.link.tree.sequences data.pos.tree
    data.link.tree.letters.product data.link.tree.sequences data.neg.tree data.collapse data.order data.positive data.nonzero η
    (fun i => parameters i ▸ data.checks i) (data.forces_l hZFC hc ρ)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双树决定性的赢家与可持久验证证书

输出的策略既赢得原正树投影，又带有反方反例树的实际序数秩。
两树地面互斥只用于从地面赢家导出反例树无枝；秩界无需小于 Woodin。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_winner_d (b : Bool) (ω A Y F T Z G S H J B W σ : M.Domain) : Prop where
  finite : Fseq_space_d I ω A H
  runs : M.IsFunctionSpace I B ω A
  turns : ∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n
  payoff : ∀ x, M.mem x W ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x
  win : Cg_win_d I b ω A H J B W σ
  certificate : Tp_certificate_d hZF b ω A (if b then Z else Y) (if b then G else F)
    (if b then S else T) H J σ

theorem tp_payoff_l (ω A Y F T B : M.Domain) :
    ∃ W, ∀ x, M.mem x W ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x := by
  let ρ : Env M 5 := ⟨fun i => [ω, A, Y, F, T].get i, fun _ => ω⟩
  let φ : UnarySchema 5 := { body := tp_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest }
  obtain ⟨W, read⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨W, fun x => (read x).trans (and_congr_right fun _ => tp_projection_sat_l I hZF.1 ..)⟩

theorem td_winner_l {ω A Γ Y F T Λ Z G S : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (disjoint : ∀ x, Tp_projection_d I ω A Y F T x → ¬ Tp_projection_d I ω A Z G S x)
    (winning : Tp_win_d hZF true true ω A Y F T ∨ Tp_win_d hZF false false ω A Z G S) :
    ∃ b H J B W σ, Td_winner_d hZF b ω A Y F T Z G S H J B W σ := by
  rcases winning with ⟨H, J, B, W, σ, hist, runs, turns, payoff, win⟩ |
    ⟨H, J, B, V, σ, hist, runs, turns, payoff, win⟩
  · have avoid x (fx : M.IsSetFunctionFromTo I x ω A) (follow : Cg_follows_d I true ω J σ x) :
        ¬ Tp_projection_d I ω A Z G S x :=
      disjoint x ((payoff x).mp (win.2 x ((runs x).mpr fx) follow)).2
    exact ⟨true, H, J, B, W, σ, hist, runs, turns, payoff, win,
      tp_certificate_l hZF hw dc pair' space' tree' hist win.1 avoid⟩
  · have avoid x (fx : M.IsSetFunctionFromTo I x ω A) (follow : Cg_follows_d I false ω J σ x) :
        ¬ Tp_projection_d I ω A Y F T x := by
      intro yes
      have enters : Tp_projection_d I ω A Z G S x := Classical.byContradiction
        (fun no => win.2 x ((runs x).mpr fx) follow ((payoff x).mpr ⟨(runs x).mpr fx, no⟩))
      exact disjoint x yes enters
    obtain ⟨W, payoff'⟩ := tp_payoff_l hZF ω A Y F T B
    exact ⟨false, H, J, B, W, σ, hist, runs, turns, payoff',
      ⟨win.1, fun x hx follow yes => avoid x ((runs x).mp hx) follow ((payoff' x).mp yes).2⟩,
      tp_certificate_l hZF hw dc pair space tree hist win.1 avoid⟩

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hM)

/-! 
双树输入所需的坍缩条件集与反向包含序可以直接由有限序列坍缩工厂生成。
这里把该工厂的四个输出保留为一个可调用接口，后续强迫覆盖生产器只需补上
有限参数检查和 `td_cover0_m` 的强迫证书。
-/
theorem td_collapse_order_l {ω δ : M.Domain} (hw : M.IsOmega ω) :
    ∃ C Q, Fseq_space_d K ω δ C ∧
      (∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r) ∧
      Cond_order_d M C Q C := by
  obtain ⟨C, Q, space, order, base⟩ := fseq_collapse_order_l hM hw δ
  exact ⟨C, Q, space, base, order⟩

/-! 给定一个正条件，有限的八个双树参数可以统一取其 check 名称。 -/
theorem td_check_env_l {ω A Y F T Z G S C p : M.Domain} (hZFC : M.Models ZFC)
    (hp : M.mem p C) :
    ∃ η : Env M 8,
      ∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i) := by
  let v : Fin 8 → M.Domain := [ω, A, Y, F, T, Z, G, S].get
  have hZF : M.Models ZF := ZFC.models_zf_l hZFC
  obtain ⟨η, checks, _⟩ := YesMetaZFC.Model.Forcing.Internal.check_env_l
    (M := M) (B := C) (n := 8) (b := p) hZF hp v
  exact ⟨η, checks⟩

/-! 由反向包含关系直接装配有限序列坍缩的条件序。 -/
theorem td_cond_order_l (hZFC : M.Models ZFC) {C Q : M.Domain}
    (order : ∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r) :
    Cond_order_d M C Q C := {
  refl := fun r hr => (order r r).mpr ⟨hr, hr, fun _ h => h⟩
  trans := fun r s t hr _ ht rs st => (order r t).mpr
    ⟨hr, ht, fun v hv => ((order r s).mp rs).2.2 v (((order s t).mp st).2.2 v hv)⟩
  zero := fun r _ rc =>
    (KP.mem_irrefl_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) C ((order r C).mp rc).2.1).elim }
/-! 把所有泛型扩张中的覆盖验证转成原模型中的强迫证书。
这是现有反射判据的专门化，输入只保留覆盖语义本身。 -/
theorem td_force_of_valid_l
    (hZFC : M.Models ZFC) {ρ : Env M 24}
    (O : Cond_order_d M (ρ.bound 13) (ρ.bound 14) (ρ.bound 13))
    (names : ∀ i, Name_d M (ρ.bound 13) ((td_names_m i).eval ρ))
    (hp : M.mem (ρ.bound 15) (ρ.bound 13))
    (hn : ρ.bound 15 ≠ ρ.bound 13)
    (valid : ∀ N : Structure.{u}, ∀ hN : N.Models ZF, ∀ η : Env N 24,
      Cond_order_d N (η.bound 13) (η.bound 14) (η.bound 13) →
      (∀ i, Name_d N (η.bound 13) ((td_names_m i).eval η)) →
      N.mem (η.bound 15) (η.bound 13) → η.bound 15 ≠ η.bound 13 →
      Formula.satisfies η (.truth : Formula 1 24) →
      ∀ U, Generic_d N (η.bound 13) (η.bound 14) (η.bound 13) U → U (η.bound 15) →
      ∀ ξ : Env (extension_l N hN (η.bound 13) (η.bound 14) (η.bound 13) U) 8,
        (∀ i, Qval_d N (η.bound 13) (η.bound 14) (η.bound 13) U
          ((td_names_m i).eval η) (ξ.bound i)) →
        Formula.satisfies ξ td_cover0_m) :
    Forces_d M (ρ.bound 13) (ρ.bound 14) (ρ.bound 13) td_cover0_m
      ⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ (ρ.bound 15) := by
  exact forces_of_generics_l td_cover0_m td_cover0_closed_l
    (.truth : Formula 1 24) (by simp only [Definitional.Formula.FreeClosed]) td_names_m
    (.bound 13) (.bound 14) (.bound 13) (.bound 15)
    (by intro i; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    valid (ZFC.models_zf_l hZFC) ρ O names hp hn (by simp only [Formula.satisfies_truth_iff])
/-! 先把不依赖覆盖强迫证书的输入字段一次性实际生成。
条件取有限序列空间中的空函数，因而自动落在 C 且严格小于 C；
八个参数的规范名称则由同一个条件上的 check 递归构造。 -/
theorem td_basic_input_l {ω δ A Y F T Z G S : M.Domain}
    (hw : M.IsOmega ω) :
    ∃ C Q p, ∃ η : Env M 8,
      Fseq_space_d K ω δ C ∧
      (∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r) ∧
      M.mem p C ∧ p ≠ C ∧
      (∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i)) := by
  obtain ⟨C, Q, collapse, order, _⟩ := td_collapse_order_l hZFC (δ := δ) hw
  let e : M.Domain := Classical.choose (KP.exists_empty (ZF.modelsKP hM))
  have empty : ∀ x, ¬M.mem x e := Classical.choose_spec (KP.exists_empty (ZF.modelsKP hM))
  have he : Num_d 0 e := empty
  have hp : M.mem e C := collapse e |>.mpr ⟨e, num_mem_l hM.1 hw he, ds_empty_fun_l K empty⟩
  have hn : e ≠ C := by
    intro eq
    exact KP.mem_irrefl_d (ZF.modelsKP hM) C (eq ▸ hp)
  obtain ⟨η, checks⟩ := td_check_env_l hZFC
    (ω := ω) (A := A) (Y := Y) (F := F) (T := T) (Z := Z) (G := G) (S := S) (C := C) (p := e) hp
  exact ⟨C, Q, e, η, collapse, order, hp, hn, checks⟩
/-- 优化稿 2.3：一次原坍缩的强迫穷尽给出地面互补、实际赢家及反方树秩。 -/
theorem td_determinacy_l {ω δ A X a Γ Y F T Λ Z G S C Q p : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d K δ) (rank : V_d K δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct K Y A Γ) (space : Fseq_space_d K ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct K Z A Λ) (space' : Fseq_space_d K ω Z G) (tree' : Tree_d G S)
    (disjoint : ∀ x, Tp_projection_d K ω A Y F T x → ¬ Tp_projection_d K ω A Z G S x)
    (collapse : Fseq_space_d K ω δ C)
    (order : ∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r)
    (hp : M.mem p C) (hn : p ≠ C) (η : Env M 8)
    (checks : ∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i))
    (force : Forces_d M C Q C td_cover0_m η p) :
    (∀ x, M.IsSetFunctionFromTo K x ω A →
      (Tp_projection_d K ω A Y F T x ↔ ¬ Tp_projection_d K ω A Z G S x)) ∧
    ∃ b H J B W σ, Td_winner_d hM b ω A Y F T Z G S H J B W σ := by
  obtain ⟨cover, winning⟩ := td_ground_l hZFC hw hd rank hA ha pair space tree pair' space' tree'
    collapse order hp hn η checks force
  exact ⟨fun x fx => ⟨disjoint x, fun no => (cover x fx).elim id (fun yes => (no yes).elim)⟩,
    td_winner_l hM hw (ZFC.dc_l K hZFC hw) pair space tree pair' space' tree' disjoint winning⟩


end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原正负查询树的互补性与实际赢家

统一小坍缩给出地面覆盖；原 8.5 的声音性把两侧投影送到真实 L(ℝ)
中的同一参数。最小坏收益唯一性排除交集，再由双树定理取得普通
投影博弈的策略和反方树秩。无需另设正负互斥或见证正确性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_cover_data_d.determinacy_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d hZF φ ρ)
    (sequence : let ν := qs_source_env_l hZF ρ data.model data.inside
      Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (data.theory.native_l I hZF data.omega))))
        (ν.bound 0) (ν.bound 1))
    (AC : ∃ i, Rd_entry_d i (ρ.bound 5) (ρ.bound 42))
    (σC : ∃ i, Rd_entry_d i (ρ.bound 9) (ρ.bound 42))
    (aC : ∃ i, Rd_entry_d i (ρ.bound 10) (ρ.bound 42))
    {V : M.Domain} (hd : Woodin_d I (ρ.bound 16)) (rank : V_d I (ρ.bound 16) V)
    (inside : M.mem (ρ.bound 0) V) :
    Td_cover_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70)
      (ρ.bound 65) (ρ.bound 68) (ρ.bound 71) ∧
    (∀ x, M.IsSetFunctionFromTo I x (ρ.bound 0) (ρ.bound 0) →
      (Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70) x ↔
        Relative.Lq_signed_d hZF φ true (ρ.bound 0) (ρ.bound 10) x) ∧
      (Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 71) x ↔
        Relative.Lq_signed_d hZF φ false (ρ.bound 0) (ρ.bound 10) x)) ∧
    ∃ b H J B W σ, Td_winner_d hZF b (ρ.bound 0) (ρ.bound 0)
      (ρ.bound 65) (ρ.bound 68) (ρ.bound 70) (ρ.bound 65) (ρ.bound 68) (ρ.bound 71) H J B W σ := by
  let N := smdl_structure_l I (R := ρ.bound 3) data.model.1.2.1
  let ν := qs_source_env_l hZF ρ data.model data.inside
  have native := ZFC.models_zf_l (data.theory.native_l I hZF data.omega)
  have seed := (qs_source_decode_l hZF hc ρ data.model data.transitive data.inside native).mp data.source_truth
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have ba := (bc_binary_image_l Subtype.val ni (smem_full_l I data.model data.transitive) native.1 hZF.1).mp seed.binary
  have sound (sign : Bool) (T : M.Domain) (tree : Qs_tree_d hZF φ sign data.link.tree (ρ.bound 9) (ρ.bound 10) T)
      (x : M.Domain) (projected : Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) T x) :
      Relative.Lq_signed_d hZF φ sign (ρ.bound 0) (ρ.bound 10) x :=
    qs_tree_truth_l hZFC hc data.model data.transitive data.rank
      (ν.bound 0) (ν.bound 1) (ν.bound 2) (ν.bound 3) (ν.bound 5) (ν.bound 6) data.omega data.theory
      sequence seed.product seed.name ba.1 data.sh data.gn data.joint data.link tree data.params AC σC aC projected
  have disjoint x (yes : Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70) x)
      (no : Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 71) x) : False :=
    (sound true _ data.pos x yes).disjoint_l hZF hc (sound false _ data.neg x no)
  obtain ⟨cover,winning⟩ := data.ground_l hZFC hc ρ hd rank inside
  refine ⟨cover,fun x fx => ⟨⟨sound true _ data.pos x,?_⟩,⟨sound false _ data.neg x,?_⟩⟩,?_⟩
  · intro yes
    exact (cover x fx).elim id (fun no => ((yes.disjoint_l hZF hc) (sound false _ data.neg x no)).elim)
  · intro no
    exact (cover x fx).elim (fun yes => ((sound true _ data.pos x yes).disjoint_l hZF hc no).elim) id
  · exact td_winner_l hZF data.omega (ZFC.dc_l I hZFC data.omega)
      data.link.tree.letters.product data.link.tree.sequences data.pos.tree
      data.link.tree.letters.product data.link.tree.sequences data.neg.tree disjoint winning

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原双树运行排除最小坏收益

任取一个真实对局，覆盖给出一侧上传见证，从中解码 L(ℝ) 内的实际
最小坏收益。所有查询仍使用同一实数参数，所以正树投影恰好刻画此收益。
双树赢家于是赢得原收益；同实数模型间的决定性绝对性将它传回 L(ℝ)，
与该收益的非决定性矛盾。整个论证消费原吸收、构枝及小坍缩覆盖的实际输出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_cover_data_d.no_minimum_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    (ρ : Env M 80) (data : Qs_cover_data_d hZF φ ρ)
    (sequence : let ν := qs_source_env_l hZF ρ data.model data.inside
      Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (data.theory.native_l I hZF data.omega))))
        (ν.bound 0) (ν.bound 1))
    (AC : ∃ i, Rd_entry_d i (ρ.bound 5) (ρ.bound 42))
    (σC : ∃ i, Rd_entry_d i (ρ.bound 9) (ρ.bound 42))
    (aC : ∃ i, Rd_entry_d i (ρ.bound 10) (ρ.bound 42))
    {V : M.Domain} (hd : Woodin_d I (ρ.bound 16)) (rank : V_d I (ρ.bound 16) V)
    (inside : M.mem (ρ.bound 0) V) : False := by
  obtain ⟨cover,truth,p,H,J,B,W,σ,winner⟩ := data.determinacy_l hZFC hc ρ sequence AC σC aC hd rank inside
  obtain ⟨_,r,_,basis⟩ := mc_nat_exists_l (ZF.modelsKP hZF) data.omega
  have fr := fn0_function_l (ZF.modelsKP hZF) basis.constant
  have query : ∃ sign, Lq_signed_d hZF φ sign (ρ.bound 0) (ρ.bound 10) r := by
    rcases cover r fr with yes | no
    · exact ⟨true,((truth r fr).1).mp yes⟩
    · exact ⟨false,((truth r fr).2).mp no⟩
  obtain ⟨sign,query⟩ := query
  obtain ⟨w,b,a,x₀,S,T,c,A,ew,ea,_,space,seed,finite,present,least,bad,_⟩ := query.native_l hZF hc
  let L := Relative.lr_model_l hZF
  have hL : L.Models ZF := Relative.lr_model_zf_l hZF
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full (t : L.Domain) (y : M.Domain) : M.mem y t.val ↔ ∃ z : L.Domain, L.mem z t ∧ z.val = y :=
    ⟨fun hy => ⟨⟨y,Relative.lr_transitive_l hZF t.property hy⟩,hy,rfl⟩,fun ⟨_,hy,eq⟩ => eq ▸ hy⟩
  -- 收益识别只在实际实数上进行；每一个实数都属于真实 L(ℝ)。
  have payoff x (fx : M.IsSetFunctionFromTo I x (ρ.bound 0) (ρ.bound 0)) :
      Tp_projection_d I (ρ.bound 0) (ρ.bound 0) (ρ.bound 65) (ρ.bound 68) (ρ.bound 70) x ↔ M.mem x A.val := by
    have fx' : M.IsSetFunctionFromTo I x w.val w.val := by simpa only [ew] using fx
    let y : L.Domain := ⟨x,Relative.lr_real_l hZF space ((space.2 x).mpr fx')⟩
    have reads p (q : Lq_signed_d hZF φ p (ρ.bound 0) (ρ.bound 10) x) : Jp_sign_d p y A := by
      have q' : Lq_signed_d hZF φ p w.val a.val y.val := by simpa only [ew,ea] using q
      exact q'.sign_l hZF hc seed finite least present
    refine ⟨fun yes => reads true (((truth x fx).1).mp yes),fun hx => ?_⟩
    exact (cover x fx).elim id (fun no => (reads false (((truth x fx).2).mp no) hx).elim)
  have agrees x (hx : M.mem x B) : M.mem x W ↔ M.mem x A.val :=
    (winner.payoff x).trans ((and_iff_right hx).trans (payoff x ((winner.runs x).mp hx)))
  have gm := cg_win_gm_l hZF winner.turns winner.win
  have win : Gm_win_d I p (ρ.bound 0) B H A.val σ := by
    refine ⟨gm.1,fun x hx follows => ?_⟩
    have result := gm.2 x hx follows
    cases p with
    | false => exact fun hxA => result ((agrees x hx).mpr hxA)
    | true => exact (agrees x hx).mp result
  have decided : Det_d I (ρ.bound 0) B H A.val := by
    cases p with
    | false => exact Or.inr ⟨σ,win⟩
    | true => exact Or.inl ⟨σ,win⟩
  -- 两侧有限历史空间及实数空间均是原完整空间；随后反射实际策略实数。
  have finite' := image_fseq_l hL hZF Subtype.val inj full seed.1.1 space.1 finite
  have finiteM : Fseq_space_d I (ρ.bound 0) (ρ.bound 0) T.val := by
    have h : Fseq_space_d I w.val w.val T.val := finite'
    simpa only [ew] using h
  have eB : B = b.val := hZF.1.eq_of_same_members _ _ (fun x => (winner.runs x).trans (by
    simpa only [ew] using (space.2 x).symm))
  have eT : H = T.val := hZF.1.eq_of_same_members _ _ (fun s => (winner.finite s).trans (finiteM s).symm)
  apply bad
  apply (det_image_l hL hZF Subtype.val inj full seed.1 finite space).mpr
  simpa only [← ew,eB,eT] using decided

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原数学输入排除顶条件上的最小坏代码

司寇伦树、泛型树、固定参数登记及正负查询树全部实际生成，再构造小坍缩、
空正条件、检查名字和有限反射输入。调用方只提供原秩源、乘积与名字、
顶条件最小性力迫以及原有的较小 Woodin，无需额外提供树或正确性证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_no_minimum_l {φ : Formula 1 4} (hc : φ.FreeClosed) {c X R θ : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (ω : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    {A₀ P V W₀ σ a₀ o κ q₀ sa sq : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω W₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A₀) (hκ : M.IsUncountableCardinal I ω.val κ.val)
    (ca : Check_d (smdl_structure_l I (R := R) source.1.2.1) o a₀ sa)
    (cq : Check_d (smdl_structure_l I (R := R) source.1.2.1) o q₀ sq)
    (minimum : Forces_d (smdl_structure_l I (R := R) source.1.2.1) P V P (dm_min_m φ)
      (⟨fun i => [σ,sa,sq].get i,fun _ => σ⟩ : Env (smdl_structure_l I (R := R) source.1.2.1) 3) o)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) ω A₀)
    {α Vα : M.Domain} (hα : Woodin_d I α) (rankα : V_d I α Vα)
    (inside : M.mem ω.val Vα) (bound : M.MemberSubset α κ.val) : False := by
  obtain ⟨e,he,_⟩ := hw.1.1
  obtain ⟨u,S,L,T,E,K,Wₛ,D,J,Ys,ds,hs,Fs,As,sh,_⟩ := sh_tree_exists_l hZFC hw source.1
    (B := e) (fun x hx => (he x hx).elim)
    (ZF.finite_countable_l I hZF hw (ZF.finite_empty_l I hZF hw he))
  obtain ⟨Zg,Yg,dg,hg,lg,rg,Fg,Ag,gn⟩ := gn_tree_exists_l hZF hw X P.val V.val
  obtain ⟨base,fb,_⟩ := ZF.exists_constantFunction hZF I (source := ω.val) ω.property
  obtain ⟨C,params,AC,σC,aC,_,Z,W,Y,a,b,c',d',l,r,F,A,joint,
      de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,link,positive,negative,pos,neg⟩ :=
    qs_context_l hZF hc hw sh gn P.property V.property A₀.property σ.property a₀.property
      (fn0_of_function_l (ZF.modelsKP hZF) fb)
  obtain ⟨Q,U,collapse,order,_⟩ := td_collapse_order_l hZFC (δ := α) hw
  obtain ⟨p,emptyP,hpω⟩ := hw.1.1
  have hp : M.mem p Q := (collapse p).mpr ⟨p,hpω,ds_empty_fun_l I emptyP⟩
  have nz : p ≠ Q := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hp)
  obtain ⟨η,data⟩ := qs_cover_context_l hZFC hc source trans rank ω hw certificate
    fa product name binary empty alphabet hκ ca cq minimum sh gn joint link pos neg params collapse bound order hp nz
  let ρ : Env M 80 := qs_cover_env_l (fun i => [
    ω.val,c,X,R,θ, -- 原源模型
    A₀.val,P.val,V.val,W₀.val,σ.val,a₀.val,o.val,κ.val,q₀.val,sa.val,sq.val,
    α,Q,U,p, -- 小坍缩及指定正条件
    u,S,L,T,E,K,Wₛ,D,J,Ys,ds,hs,Fs,As, -- 司寇伦树
    Zg,Yg,dg,hg,lg,rg,Fg,Ag,C, -- 泛型树及登记列
    Z,W,Y,a,b,c',d',l,r,F,A, -- 联合树
    de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,positive,negative].get i) η
  exact data.no_minimum_l hZFC hc ρ sequence AC σC aC hα rankα inside

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际派生最小坏代码自动送入原顶条件矛盾

派生最小代码先由无新序数定理回收到出发模型，尾部齐性实际构造空顶条件
上的统一最小性判定。十二项原资料随同一返回初等图整体运输，再在真实
秩层调用双树排除。出发模型自身不要求是背景秩层，也不要求有背景不可数基数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_no_derived_minimum_l {φ : Formula 1 4} (hc : φ.FreeClosed) {c X R θ : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (native : N.Models ZF) (e : N.Domain → (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (elem : Pe_d e) (ω : N.Domain) (hwN : N.IsOmega ω)
    (hw : M.IsOmega (e ω).val) (certificate : Zc_model_d I (e ω).val c X R)
    {A₀ P V W₀ σ a₀ o κ : N.Domain}
    (fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A₀ ω W₀)
    (product : Fp_product_d native ω A₀ P V) (name : Rp_name_d native ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ N.mem x o)
    (alphabet : Entry_d N o κ A₀) (hκ : M.IsUncountableCardinal I (e ω).val (e κ).val)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP native)) ω A₀)
    {α Vα : M.Domain} (hα : Woodin_d I α) (rankα : V_d I α Vα)
    (inside : M.mem (e ω).val Vα) (bound : M.MemberSubset α (e κ).val) :
    let hN := native
    ∀ G, ∀ generic : Generic_d N P V P G,
      ∀ j : N.Domain → (extension_l N hN P V P G).Domain,
        (∀ a, Gval_d N P V P G a (j a)) →
        ∀ Z q, Qval_d N P V P G σ Z →
          ¬ Dm_min_d (preserves_zf_l (product.order_l hN) hN generic) φ Z (j a₀) q := by
  dsimp only
  intro G generic j ground Z q value minimum
  have target := ZFC.models_zf_l (certificate.native_l I hZF hw)
  obtain ⟨q₀,o',sa,sq,_,empty',ca,cq,_,forced,_⟩ :=
    name.minimum_top_l native hc hwN fa.1 product generic j ground value minimum
  have eq : o' = o := native.1.eq_of_same_members _ _ (fun x => iff_of_false (empty' x) (empty x))
  subst o'
  -- 统一原一阶公式同时搬运名字、检查名字和实际力迫，保留同一参数。
  let ρ : Env N 12 := ⟨fun i => [ω,A₀,P,V,W₀,σ,a₀,o,κ,q₀,sa,sq].get i,fun _ => σ⟩
  have data : Qs_source_d native φ ρ := ⟨fa,product,name,binary,empty,alphabet,ca,cq,forced⟩
  have moved := (qs_source_sat_l target hc (image_env_l e ρ)).mp
    ((elem (qs_source_m φ) (qs_source_closed_l hc) ρ).mp ((qs_source_sat_l native hc ρ).mpr data))
  have sequence' := sequence.image_l (kp_pair_l (ZF.modelsKP native))
    (kp_pair_l (ZF.modelsKP target)) native.1 target.1 e elem
  exact qs_no_minimum_l hZFC hc source trans rank (e ω) hw certificate moved.function moved.product
    moved.name moved.binary moved.empty moved.alphabet hκ moved.a_check moved.q_check moved.minimum
    sequence' hα rankα inside bound

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定原地实数参数的实际派生收益决定性

原参数的检查名字已在零前缀给出 R* 成员。无新实数定理实际构造派生模型
的完整 Baire 空间和种子，再对同一参数、任意序数代码呈示的收益证明决定性。
反设不决定时构造最小坏代码，沿实际返回初等图送入真实秩层的顶条件排除。
秩层前提只约束返回目标，因此也适用于可数迭代模型自身的派生层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_derived_det_l {φ : Formula 1 4} (hc : φ.FreeClosed) {c X R d Y S₀ θ π K : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (target : Smem_d I d Y S₀) (rank : V_d I θ Y) (returned : Smap_d I ω.val c d X Y π)
    {A₀ P V W₀ σ a₀ o κ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω W₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A₀)
    (image : Rd_entry_d κ.val K π) (hK : M.IsUncountableCardinal I ω.val K)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) ω A₀)
    {α Vα : M.Domain} (hα : Woodin_d I α) (rankα : V_d I α Vα)
    (inside : M.mem ω.val Vα) (bound : M.MemberSubset α K) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let hN := ZFC.models_zf_l (certificate.native_l I hZF hw)
    ∀ G, ∀ generic : Generic_d N P V P G,
      ∀ j : N.Domain → (extension_l N hN P V P G).Domain,
        (∀ a, Gval_d N P V P G a (j a)) →
        ∀ Z, Qval_d N P V P G σ Z → ∀ S, ∀ tc : Tc_d Z S,
          let hE := preserves_zf_l (product.order_l hN) hN generic
          let D := Relative.la_model_l S (ZF.models_kpi_l hE)
          let hD := Relative.la_model_zf_l S hE tc.1
          let J := kp_pair_l (ZF.modelsKP hD)
          ∃ w b s T a : D.Domain, w.val = j ω ∧ b.val = Z ∧ s.val = S ∧ a.val = j a₀ ∧
            Lr_seed_d hD w b s ∧ Fseq_space_d J w w T ∧ D.mem a b ∧
            ∀ q A, Jp_d J φ s b a q A → Det_d J w b T A := by
  dsimp only
  intro G generic j ground Z value S tc
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  let nx : Nonempty {x // M.mem x X} := ⟨ω⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ω,fun _ => ω⟩
  have hwN : N.IsOmega ω := (Formula.satisfies_isOmega_iff _ .newest).mp
    ((smem_formula_l I source nx (Formula.isOmega .newest) ρ).mp
      ((Formula.satisfies_isOmega_iff ρ .newest).mpr (rt_omega_l trans nx hZF.1 ω hw)))
  -- 返回图实际生产初等映射及目标 ZFC；不可数性只用于真实返回像 K。
  obtain ⟨e,elem,values⟩ := returned.project_l I hZF hw source.1 target.1
  have eqω : (e ω).val = ω.val := returned.1.1.1.2 _ _ _ (values ω)
    (returned.omega_l I hZF hw trans (v_transitive_l I rank) source target ω.property)
  have eqκ : (e κ).val = K := returned.1.1.1.2 _ _ _ (values κ) image
  have hw' : M.IsOmega (e ω).val := eqω.symm ▸ hw
  have cert' : Zc_model_d I (e ω).val d Y S₀ := eqω.symm ▸ certificate.map_l hZF hw target.1 returned
  have card : M.IsUncountableCardinal I (e ω).val (e κ).val := by simpa only [eqω,eqκ] using hK
  let E := extension_l N native P V P G
  have hE : E.Models ZF := preserves_zf_l (product.order_l native) native generic
  let D := Relative.la_model_l (M := E) S (ZF.models_kpi_l hE)
  have hD : D.Models ZF := Relative.la_model_zf_l (M := E) S hE tc.1
  let J := kp_pair_l (ZF.modelsKP hD)
  obtain ⟨j',ground',_,models⟩ := name.derived_model_l native (G := G) (Z := Z) hwN fa product generic value
  have eqj : j' = j := funext fun a => (ground' a).unique_l (product.order_l native) native generic (ground a)
  subst j'
  obtain ⟨w,b,s,ew,eb,es,seed,_⟩ := models S tc
  obtain ⟨T,finite⟩ := ZF.fseq_space_exists_l J hD seed.1.1 w
  have ha := name.ground_real_l native hwN fa product generic j ground value binary.1
  let a : D.Domain := ⟨j a₀,Relative.la_transitive_l (M := E) S (ZF.models_kpi_l hE) tc.1 b.property (eb.symm ▸ ha)⟩
  have real : D.mem a b := by
    change E.mem (j a₀) b.val
    exact eb.symm ▸ ha
  refine ⟨w,b,s,T,a,ew,eb,es,rfl,seed,finite,real,fun q A present => ?_⟩
  apply Classical.byContradiction
  intro bad
  have failed : Jp_bad_d J φ w s b T a q := ⟨A,present,bad⟩
  obtain ⟨d,least⟩ := jp_min_l hD (φ := φ) (ω := w) (S := s) (B := b) (T := T) (a := a) (c := q) hc failed
  have minimum : Dm_min_d hE φ Z (j a₀) d.val := ⟨S,tc,b,a,d,eb,rfl,rfl,real,w,s,T,seed.1,seed.2,finite,least⟩
  exact qs_no_derived_minimum_l hZFC hc target (v_transitive_l I rank) rank native e elem ω hwN hw' cert'
    fa product name binary empty alphabet card sequence hα rankα (eqω.symm ▸ inside) (eqκ.symm ▸ bound)
    G generic j ground Z d.val value minimum

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一双树胜策在传递外模型中保持

目标重新构造其全部对局和正树投影收益集，策略及反例树秩仍是原对象的像。
I 的情形用目标中的两树覆盖；II 的情形仅凭反例树秩即可排除正树投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "K" => kp_pair_l (ZF.modelsKP hN)
include hi he

/-- 输出同一 e(σ) 的目标获胜性；目标只需 ZF，I 的分支才使用覆盖。 -/
theorem Td_winner_d.outward_l {b : Bool} {ω A Y F T Z G S H J B W σ : M.Domain}
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (winner : Td_winner_d hM b ω A Y F T Z G S H J B W σ)
    (cover : b = true → Td_cover_d K (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S)) :
    ∃ B' W', Td_winner_d hN b (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S) (e H) (e J) B' W' (e σ) := by
  have hwN := image_omega_l (hEN := hN.1) e hi he hM
    (fun _ hn => KP.mem_minimal_exists_d (ZF.modelsKP hN) hn) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  have hist := image_fseq_l hM hN e hi he hw hwN winner.finite
  have finite := image_fseq_l hM hN e hi he hw hwN space
  have finite' := image_fseq_l hM hN e hi he hw hwN space'
  have opposite : Fseq_space_d I ω (if b then Z else Y) (if b then G else F) := by
    cases b <;> assumption
  have cert := winner.certificate.image_l hM hN e hi he opposite winner.finite
  have cert' : Tp_certificate_d hN b (e ω) (e A) (if b then e Z else e Y)
      (if b then e G else e F) (if b then e S else e T) (e H) (e J) (e σ) := by
    cases b <;> exact cert
  have turns n : N.mem n (e J) ↔ N.mem n (e ω) ∧ Gm_even_d K (e ω) n := by
    constructor
    · intro hn
      obtain ⟨k, hk, rfl⟩ := (he J n).mp hn
      obtain ⟨hkw, even⟩ := (winner.turns k).mp hk
      exact ⟨(image_member_l e hi he).mpr hkw, (image_even_l hM hN e hi he hw).mp even⟩
    · rintro ⟨hn, even⟩
      obtain ⟨k, hk, rfl⟩ := (he ω n).mp hn
      exact (image_member_l e hi he).mpr ((winner.turns k).mpr
        ⟨hk, (image_even_l hM hN e hi he hw).mpr even⟩)
  obtain ⟨B', runs⟩ := ZF.exists_functionSpace hN K (e ω) (e A)
  obtain ⟨W', payoff⟩ := tp_payoff_l hN (e ω) (e A) (e Y) (e F) (e T) B'
  refine ⟨B', W', hist, runs, turns, payoff, ⟨cert'.1, ?_⟩, cert'⟩
  intro x hx follows
  have fx := (runs x).mp hx
  cases b
  · intro yes
    exact cert'.avoid_l hN hwN finite (image_tree_l e hi he tree) hist fx follows ((payoff x).mp yes).2
  · apply (payoff x).mpr ∘ And.intro hx
    exact (cover rfl x fx).elim id (fun yes =>
      (cert'.avoid_l hN hwN finite' (image_tree_l e hi he tree') hist fx follows yes).elim)

end YesMetaZFC.SetTheory.LargeCardinal
