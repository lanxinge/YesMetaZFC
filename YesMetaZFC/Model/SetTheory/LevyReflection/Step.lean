import YesMetaZFC.Model.SetTheory.LevyReflection.Collection
import YesMetaZFC.SetTheory.CumulativeSelection

/-! # 有限反射族的确定增长步

有限多个见证界先取并。再在最早含有足够见证界的累积层中取整个 V 层，得到
唯一的增长步；不选择单个见证，也不要求模型具有全局良序。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

abbrev Lr_family := List (Σ n, UnarySchema n)

def Lr_step_d (Φ : Lr_family) (X Y : M.Domain) : Prop := ∀ q ∈ Φ, Lr_bound_d q.2 X Y

def lr_step_m {d} (Φ : Lr_family) (X Y : Term d) : Formula 1 d :=
  match Φ with
  | [] => .truth
  | q :: Φ => .conj (lr_bound_m q.2 X Y) (lr_step_m Φ X Y)

@[simp] theorem lr_step_closed_l {d} (Φ : Lr_family) (X Y : Term d)
    (hX : X.freeSupport = []) (hY : Y.freeSupport = []) : (lr_step_m Φ X Y).FreeClosed := by
  induction Φ with
  | nil => simp only [lr_step_m, Definitional.Formula.FreeClosed]
  | cons q Φ ih =>
    simp only [lr_step_m, Definitional.Formula.FreeClosed]
    exact ⟨lr_bound_closed_l _ _ _ hX hY, ih⟩

theorem lr_step_sat_l {d} (Φ : Lr_family) (ρ : Env M d) (X Y : Term d) :
    Formula.satisfies ρ (lr_step_m Φ X Y) ↔ Lr_step_d Φ (X.eval ρ) (Y.eval ρ) := by
  induction Φ with
  | nil => simp [lr_step_m, Lr_step_d, Formula.satisfies_truth_iff]
  | cons q Φ ih =>
    simp only [lr_step_m, Formula.satisfies_conj_iff, lr_bound_sat_l, ih, Lr_step_d, List.mem_cons]
    exact ⟨fun h r hr => hr.elim (fun hr => hr ▸ h.1) (h.2 r),
      fun h => ⟨h q (Or.inl rfl), fun r hr => h r (Or.inr hr)⟩⟩

theorem Lr_step_d.mono_l {Φ X Y A B} (h : @Lr_step_d M Φ X Y)
    (hA : M.MemberSubset A X) (hB : M.MemberSubset Y B) : Lr_step_d Φ A B :=
  fun q hq => (h q hq).mono_l hA hB

include I in
theorem ZF.lr_step_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    (Φ : Lr_family) (X : M.Domain) : ∃ Y, Lr_step_d Φ X Y := by
  induction Φ with
  | nil => exact ⟨X, fun q hq => (List.not_mem_nil hq).elim⟩
  | cons q Φ ih =>
    obtain ⟨Y, hY⟩ := lr_bound_exists_l I hZF hω X q.2
    obtain ⟨Z, hZ⟩ := ih
    obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (modelsKP hZF) Y Z
    exact ⟨W, fun r hr => (List.mem_cons.mp hr).elim
      (fun he => he ▸ hY.mono_l (fun _ h => h) (fun x hx => (hW x).mpr (Or.inl hx)))
      (fun hr => (hZ r hr).mono_l (fun _ h => h) (fun x hx => (hW x).mpr (Or.inr hx)))⟩

def lr_cover_s (Φ : Lr_family) : UnarySchema 1 := {
  body := .conj (.mem (.bound 1) .newest) (lr_step_m Φ (.bound 1) .newest) }

theorem lr_cover_sat_l (Φ : Lr_family) (ρ : Env M 1) (Y : M.Domain) :
    (lr_cover_s Φ).denote ρ Y ↔ M.mem (ρ.bound 0) Y ∧ Lr_step_d Φ (ρ.bound 0) Y := by
  simp only [lr_cover_s, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, lr_step_sat_l]
  rfl

def Lr_next_d (Φ : Lr_family) (X Y : M.Domain) : Prop := ∃ α S,
  V_min_d I (lr_cover_s Φ) ⟨fun _ => X, fun _ => X⟩ α S ∧ V_d I α Y

def lr_next_m {d} (Φ : Lr_family) (X Y : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj
    (v_min_m 𝒞 (lr_cover_s Φ) (fun _ => X.weaken.weaken) (.bound 1) .newest)
    (v_m 𝒞 (.bound 1) Y.weaken.weaken)))

@[simp] theorem lr_next_closed_l {d} (Φ : Lr_family) (X Y : Term d)
    (hX : X.freeSupport = []) (hY : Y.freeSupport = []) : (lr_next_m (𝒞 := 𝒞) Φ X Y).FreeClosed := by
  simp -implicitDefEqProofs [lr_next_m, Definitional.Formula.FreeClosed, *]

theorem lr_next_sat_l (hE : Extensional M) {d} (Φ : Lr_family) (ρ : Env M d) (X Y : Term d) :
    Formula.satisfies ρ (lr_next_m (𝒞 := 𝒞) Φ X Y) ↔ Lr_next_d I Φ (X.eval ρ) (Y.eval ρ) := by
  simp only [lr_next_m, Lr_next_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_min_sat_l I hE, v_sat_l I hE, Definitional.Term.eval_weaken]
  apply exists_congr
  intro α
  apply exists_congr
  intro S
  apply and_congr_left
  intro _
  apply v_min_congr_l I
  intro W
  exact (lr_cover_sat_l Φ _ W).trans
    (lr_cover_sat_l Φ (⟨fun _ => X.eval ρ, fun _ => X.eval ρ⟩ : Env M 1) W).symm

theorem ZF.lr_next_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    (Φ : Lr_family) (X : M.Domain) : ∃ Y, Lr_next_d I Φ X Y := by
  obtain ⟨W, hw⟩ := lr_step_exists_l I hZF hω Φ X
  obtain ⟨Z, hZ⟩ := KP.exists_insert (modelsKP hZF) W X
  have hz := (lr_cover_sat_l Φ (⟨fun _ => X, fun _ => X⟩ : Env M 1) Z).mpr
    ⟨(hZ X).mpr (Or.inr rfl), hw.mono_l (fun _ h => h) (fun x hx => (hZ x).mpr (Or.inl hx))⟩
  obtain ⟨α, S, hs⟩ := v_min_exists_l I hZF (lr_cover_s Φ) ⟨fun _ => X, fun _ => X⟩ ⟨Z, hz⟩
  obtain ⟨V, hV, hr⟩ := hs
  exact ⟨V, α, S, ⟨V, hV, hr⟩, hV⟩

theorem Lr_next_d.unique_l (hZF : M.Models ZF) {Φ X Y Z}
    (h : Lr_next_d I Φ X Y) (k : Lr_next_d I Φ X Z) : Y = Z := by
  obtain ⟨α, S, hs, hy⟩ := h
  obtain ⟨β, T, ht, hz⟩ := k
  obtain ⟨rfl, _⟩ := ZF.v_min_unique_l I hZF hs ht
  exact ZF.v_unique_l I hZF hy hz

theorem Lr_next_d.cover_l (hZF : M.Models ZF) {Φ X Y} (h : Lr_next_d I Φ X Y) :
    (∃ α, V_d I α Y) ∧ M.mem X Y ∧ Lr_step_d Φ X Y := by
  obtain ⟨α, S, hs, hy⟩ := h
  obtain ⟨V, hv, ⟨Z, hz⟩, hS, _⟩ := hs
  have he := ZF.v_unique_l I hZF hv hy
  subst V
  obtain ⟨hzY, hZ⟩ := (hS Z).mp hz
  obtain ⟨hXZ, hstep⟩ := (lr_cover_sat_l Φ _ Z).mp hZ
  exact ⟨⟨α, hy⟩, ZF.v_transitive_l I hZF hy Z hzY X hXZ,
    hstep.mono_l (fun _ h => h) (ZF.v_transitive_l I hZF hy Z hzY)⟩

end YesMetaZFC.SetTheory
