import YesMetaZFC.SetTheory.InnerModel.Order.Projection

/-! # 载体与良序的配对状态算子

微后继的两个输出共同编码为一个实际集合，供已有的内部成员递归使用。
坐标读取、构造见证及输出配对均在同一 Σ₁ 正规形内验证。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_state_d (p q : M.Domain) : Prop := ∃ U R V S,
  Rp_proj_d false p U ∧ Rp_proj_d true p R ∧ Rw_successor_d U R V S ∧ KPair_d M q V S

def rw_state_s : S1_binary 0 where
  matrix := {
    -- 量词后的槽位为 W,S,V,R,U,T,q,p。
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
        .conj (rp_proj_m false (.bound 7) (.bound 4)) <|
          .conj (rp_proj_m true (.bound 7) (.bound 3)) <|
            .conj (rw_successor_s.matrix_m (Fin.cases (.bound 3) (fun _ => .bound 1)) (.bound 4) (.bound 2) .newest)
              (kpair0_m (.bound 6) (.bound 2) (.bound 1))
    freeClosed := by
      have h : (rw_successor_s.matrix_m (Fin.cases (.bound 3) (fun _ => .bound 1))
          (.bound 4) (.bound 2) .newest : Formula 1 8).FreeClosed :=
        S1_binary.matrix_closed_l _ _ _ _ _ (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, h]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (rp_proj_delta_l ..) (.conj (rp_proj_delta_l ..)
        (.conj (rw_successor_s.matrix.delta0.bind_l _) (kpair0_delta_l ..)))))))) }

def Rw_state_cert_d (T p q : M.Domain) : Prop := ∃ U, M.mem U T ∧ ∃ R, M.mem R T ∧ ∃ V, M.mem V T ∧
  ∃ S, M.mem S T ∧ ∃ W, M.mem W T ∧ Rp_proj_d false p U ∧ Rp_proj_d true p R ∧
    Rw_successor_cert_d W U R V S ∧ KPair_d M q V S

theorem rw_state_matrix_l (hKP : M.Models KP) (ρ : Env M 0) (p q T : M.Domain) :
    Formula.satisfies (((ρ.push p).push q).push T) rw_state_s.matrix.body ↔ Rw_state_cert_d T p q := by
  simp only [rw_state_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rp_proj_sat_l hKP.1, kpair0_sat_l hKP.1, rw_successor_matrix_formula_l hKP]
  rfl

theorem rw_state_sat_l (hKP : M.Models KP) (ρ : Env M 0) (p q : M.Domain) :
    rw_state_s.schema.denote ρ p q ↔ Rw_state_d p q := by
  rw [S1_binary.sat_l]
  simp only [rw_state_matrix_l hKP]
  constructor
  · rintro ⟨_, U, _, R, _, V, _, S, _, W, _, hu, hr, hw, hq⟩
    exact ⟨U, R, V, S, hu, hr, rw_successor_cert_sound_l hw, hq⟩
  · rintro ⟨U, R, V, S, hu, hr, h, hq⟩
    obtain ⟨W, hw⟩ := rw_successor_cert_exists_l hKP h
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [U, R, V, S, W]
    exact ⟨T, U, (ht U (by simp)).2, R, (ht R (by simp)).2, V, (ht V (by simp)).2,
      S, (ht S (by simp)).2, W, (ht W (by simp)).2, hu, hr, hw, hq⟩

theorem rw_state_total_l (hKP : M.Models KP) (p : M.Domain) : ∃ q, Rw_state_d p q := by
  obtain ⟨U, hu⟩ := rp_proj_total_l hKP false p
  obtain ⟨R, hr⟩ := rp_proj_total_l hKP true p
  obtain ⟨V, S, h⟩ := rw_successor_exists_l hKP U R
  obtain ⟨q, hq⟩ := (kp_pair_l hKP).total V S
  exact ⟨q, U, R, V, S, hu, hr, h, hq⟩

theorem rw_state_unique_l (hE : Extensional M) {p q r : M.Domain} (h : Rw_state_d p q) (g : Rw_state_d p r) : q = r := by
  obtain ⟨U, R, V, S, hu, hr, h, hq⟩ := h
  obtain ⟨U', R', V', S', hu', hr', g, hrq⟩ := g
  have he := rp_proj_unique_l hE hu hu'; subst U'
  have he := rp_proj_unique_l hE hr hr'; subst R'
  obtain ⟨rfl, rfl⟩ := rw_successor_unique_l hE h g
  exact kpair_unique_l M hE hq hrq

theorem rw_state_pair_l (hE : Extensional M) {p q U R V S : M.Domain}
    (hp : KPair_d M p U R) (hq : KPair_d M q V S) : Rw_state_d p q ↔ Rw_successor_d U R V S := by
  constructor
  · rintro ⟨A, B, C, D, ha, hb, h, hq'⟩
    have he : A = U := (rp_proj_pair_l hE hp false).mp ha; subst A
    have he : B = R := (rp_proj_pair_l hE hp true).mp hb; subst B
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq' hq
    exact h
  · exact fun h => ⟨U, R, V, S, (rp_proj_pair_l hE hp false).mpr rfl, (rp_proj_pair_l hE hp true).mpr rfl, h, hq⟩

end YesMetaZFC.SetTheory.InnerModel
