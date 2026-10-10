import YesMetaZFC.SetTheory.InnerModel.Order.Operator
import YesMetaZFC.SetTheory.InnerModel.Order.StateLocal

/-! # 递归算子证书的实际中间集合

从复合正规形逐层读取值域、后继像、两个坐标像及它们的并，保留后继计算的
共同见证界。反向装配只使用这些已取得的集合与见证。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rp_image_d (i : Bool) (X D : M.Domain) : Prop :=
  ∀ A, M.mem A D ↔ ∃ p, M.mem p X ∧ Rp_proj_d i p A

theorem rp_image_union_l {i : Bool} {X D U : M.Domain} (hd : Rp_image_d i X D) (hu : Rp_union_d i X U) :
    Rd_fun_d .union D D D U := by
  intro x; apply (hu x).trans
  exact ⟨fun ⟨p, hp, A, ha, hx⟩ => ⟨A, (hd A).mpr ⟨p, hp, ha⟩, hx⟩,
    fun ⟨A, ha, hx⟩ => ((hd A).mp ha).elim (fun p hp => ⟨p, hp.1, A, hp.2, hx⟩)⟩

theorem rp_image_bounded_l (hKP : M.Models KP) {C B X : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hBC : M.mem B C) (hb : M.TransitiveSet B) (hXC : M.mem X C)
    (hx : M.MemberSubset X B) (i : Bool) (ρ : Env M 0)
    (hv : ∀ p, M.mem p X → ∀ v, Rp_proj_d i p v → M.mem v B) :
    ∃ D, M.mem D C ∧ M.MemberSubset D B ∧ Rp_image_d i X D := by
  obtain ⟨D, hDC, hd⟩ := si_bounded_image_l hKP hC hc hBC hb hXC hx (S1_binary.of_delta0 (rp_proj_s i)) ρ
  refine ⟨D, hDC, fun v h => ((hd v).mp h).1, fun v => ?_⟩
  rw [hd v]
  simp only [S1_binary.of_delta0_matrix_l, rp_proj_schema_l hKP.1]
  exact ⟨fun ⟨_, p, hp, _, _, h⟩ => ⟨p, hp, h⟩,
    fun ⟨p, hp, h⟩ => ⟨hv p hp v h, p, hp, p, hx p hp, h⟩⟩

theorem rp_image_matrix_value_l (hKP : M.Models KP) (ρ : Env M 0) (i : Bool) {X D B : M.Domain}
    (h : Formula.satisfies (((ρ.push X).push D).push B) (S1_binary.of_delta0 (rp_proj_s i)).image.matrix.body) :
    Rp_image_d i X D := by
  have hp := (S1_binary.image_sat_l hKP (S1_binary.of_delta0 (rp_proj_s i)) ρ X D
    (fun p _ => (rp_proj_total_l hKP i p).imp fun x hx =>
      (S1_binary.of_delta0_sat_l _ ρ p x).mpr ((rp_proj_schema_l hKP.1 ρ i p x).mpr hx))
    (fun _ _ _ _ h g => rp_proj_unique_l hKP.1
      ((rp_proj_schema_l hKP.1 ..).mp ((S1_binary.of_delta0_sat_l ..).mp h))
      ((rp_proj_schema_l hKP.1 ..).mp ((S1_binary.of_delta0_sat_l ..).mp g)))).mp
    ((S1_binary.sat_l _ ρ X D).mpr ⟨B, h⟩)
  simpa only [Rp_image_d, S1_binary.of_delta0_sat_l, rp_proj_schema_l hKP.1] using hp

def Rw_parts_d (ρ : Env M 0) (B F p : M.Domain) : Prop := ∃ X Y D E U R,
  M.mem X B ∧ M.mem Y B ∧ M.mem D B ∧ M.mem E B ∧ M.mem U B ∧ M.mem R B ∧
  Rd_fun_d .range F F F X ∧ Rp_image_d false Y D ∧ Rp_image_d true Y E ∧
  Rd_fun_d .union D D D U ∧ Rd_fun_d .union E E E R ∧ KPair_d M p U R ∧
    Formula.satisfies (((ρ.push X).push Y).push B) rw_state_s.image.matrix.body

theorem rw_op_read_l (hKP : M.Models KP) (ρ : Env M 0) {T B F p : M.Domain}
    (ht : M.TransitiveSet T) (hB : M.mem B T)
    (h : Formula.satisfies (((ρ.push F).push p).push B) rw_op_s.matrix.body) : Rw_parts_d ρ T F p := by
  obtain ⟨X, hXB, w, _, v, hvB, hX, hv⟩ := (S1_binary.comp_matrix_l _ _ ρ F p B).mp h
  have hvT := ht B hB v hvB
  obtain ⟨Y, hYv, w', hWv, v', hv'v, hY, hv'⟩ := (S1_binary.comp_matrix_l _ _ ρ X p v).mp hv
  have hJoinT := ht v hvT v' hv'v
  obtain ⟨U, hUv', R, hRv', a, hav', b, hbv', ha, hb, hp⟩ := (S1_binary.pair_matrix_l hKP.1 _ _ ρ Y p v').mp hv'
  have haT := ht v' hJoinT a hav'
  have hbT := ht v' hJoinT b hbv'
  obtain ⟨D, hDa, d, _, e, _, hd, hu⟩ := (S1_binary.comp_matrix_l _ _ ρ Y U a).mp ha
  obtain ⟨E, hEb, f, _, g, _, hf, hr⟩ := (S1_binary.comp_matrix_l _ _ ρ Y R b).mp hb
  have unary k x y z (hz : Formula.satisfies (((ρ.push x).push y).push z) (rd_unary_s k).matrix.body) :
      Rd_fun_d k x x x y := (rd_unary_sat_l hKP k ρ x y).mp ((S1_binary.sat_l _ ρ x y).mpr ⟨z, hz⟩)
  refine ⟨X, Y, D, E, U, R, ht B hB X hXB, ht v hvT Y hYv, ht a haT D hDa, ht b hbT E hEb,
    ht v' hJoinT U hUv', ht v' hJoinT R hRv', unary _ _ _ w hX,
    rp_image_matrix_value_l hKP ρ false hd, rp_image_matrix_value_l hKP ρ true hf,
    unary _ _ _ e hu, unary _ _ _ g hr, hp, ?_⟩
  obtain ⟨h, g⟩ := (rw_state_s.image_matrix_l ρ X Y w').mp hY
  apply (rw_state_s.image_matrix_l ρ X Y T).mpr
  have inT z hz := ht w' (ht v hvT w' hWv) z hz
  exact ⟨fun x hx => (h x hx).imp (fun y hy => ⟨hy.1, hy.2.imp (fun z hz => ⟨inT z hz.1, hz.2⟩)⟩),
    fun y hy => (g y hy).imp (fun x hx => ⟨hx.1, hx.2.imp (fun z hz => ⟨inT z hz.1, hz.2⟩)⟩)⟩

theorem rw_op_in_l (hKP : M.Models KP) {C B F p : M.Domain} (hC : Rd_closed_d C)
    (hBC : M.mem B C) (hb : M.TransitiveSet B) (ρ : Env M 0) (h : Rw_parts_d ρ B F p) :
    Si_cert_d C rw_op_s ρ F p := by
  obtain ⟨X, Y, D, E, U, R, hX, hY, hD, hE, hU, hR, hx, hd, he, hu, hr, hp, hs⟩ := h
  have enclosed x hx : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem x A := ⟨B, hBC, hb, hx⟩
  have unary k x y (hy : M.mem y B) (h : Rd_fun_d k x x x y) : Si_cert_d C (rd_unary_s k) ρ x y :=
    si_delta_l _ ρ (enclosed y hy) ((rd_graph_sat_l hKP _ _ _ _ _ _).mpr h)
  have projection i A (hA : M.mem A B) (ha : Rp_image_d i Y A) :
      Si_cert_d C (S1_binary.of_delta0 (rp_proj_s i)).image ρ Y A := by
    apply si_image_l hKP hC hBC hb (enclosed A hA) _ ρ
    · intro q hq
      obtain ⟨z, hz⟩ := rp_proj_total_l hKP i q
      exact ⟨z, (ha z).mpr ⟨q, hq, hz⟩, q, hb Y hY q hq,
        (S1_binary.of_delta0_matrix_l _ ρ q z q).mpr ((rp_proj_schema_l hKP.1 ρ i q z).mpr hz)⟩
    · intro z hz
      obtain ⟨q, hq, hz⟩ := (ha z).mp hz
      exact ⟨q, hq, q, hb Y hY q hq,
        (S1_binary.of_delta0_matrix_l _ ρ q z q).mpr ((rp_proj_schema_l hKP.1 ρ i q z).mpr hz)⟩
  have left : Si_cert_d C (rp_union_s false) ρ Y U := si_comp_l hKP hC (projection false D hD hd) (unary .union D U hU hu)
  have right : Si_cert_d C (rp_union_s true) ρ Y R := si_comp_l hKP hC (projection true E hE he) (unary .union E R hR hr)
  have joined : Si_cert_d C rw_join_s ρ Y p := si_pair_l hKP hC left right hp
  have im := (rw_state_s.image_matrix_l ρ X Y B).mp hs
  have stepped := si_image_l hKP hC hBC hb (enclosed Y hY) rw_state_s ρ im.1 im.2
  exact si_comp_l hKP hC (unary .range F X hX hx) (si_comp_l hKP hC stepped joined)

end YesMetaZFC.SetTheory.InnerModel
