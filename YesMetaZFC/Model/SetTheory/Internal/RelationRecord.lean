import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Internal.RelationRelative

/-! # 原关系模型中的完整记录与元组

背景只保存载体、关系和对象码。全部坐标先检查所属，再在原关系结构中
解释原公式；元组的配对也是该结构的配对。高层记录不经过共同低层实现。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def rr_params_m {d} : {n : Nat} → (Fin n → Term d) → Term d → Formula 1 d
  | 0, _, _ => .truth
  | n+1, v, X => .conj (.mem (v 0) X) (rr_params_m (n := n) (fun i => v i.succ) X)

theorem rr_params_closed_l {d n} (v : Fin n → Term d) (X : Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hX : X.freeSupport = []) : (rr_params_m v X).FreeClosed := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨⟨hv 0, hX⟩, ih (fun i => v i.succ) (fun i => hv i.succ)⟩

theorem rr_params_sat_l {d n} (ρ : Env M d) (v : Fin n → Term d) (X : Term d) :
    Formula.satisfies ρ (rr_params_m v X) ↔ ∀ i, M.mem ((v i).eval ρ) (X.eval ρ) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    rw [rr_params_m, Formula.satisfies_conj_iff, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

def Rr_truth_d {n} (X R : M.Domain) (φ : Formula 1 (n+1)) (v : Fin (n+1) → M.Domain) : Prop :=
  ∃ h : ∀ i, M.mem (v i) X,
    Formula.satisfies (⟨fun i => ⟨v i, h i⟩, fun _ => ⟨v 0, h 0⟩⟩ :
      Env (smdl_structure_l I (R := R) ⟨v 0, h 0⟩) (n+1)) φ

def rr_truth_m {d n} (φ : Formula 1 (n+1)) (X R : Term d) (v : Fin (n+1) → Term d) : Formula 1 d :=
  .conj (rr_params_m v X) (rr_rel_m 𝒞 φ X R v)

theorem rr_truth_closed_l {d n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R : Term d) (v : Fin (n+1) → Term d) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) : (rr_truth_m (𝒞 := 𝒞) φ X R v).FreeClosed :=
  ⟨rr_params_closed_l v X hv hX, rr_rel_closed_l 𝒞 φ closed X R v hX hR hv⟩

theorem rr_truth_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R : Term d) (v : Fin (n+1) → Term d) :
    Formula.satisfies ρ (rr_truth_m (𝒞 := 𝒞) φ X R v) ↔
      Rr_truth_d I (X.eval ρ) (R.eval ρ) φ (fun i => (v i).eval ρ) := by
  rw [rr_truth_m, Formula.satisfies_conj_iff, rr_params_sat_l]
  have read (h : ∀ i, M.mem ((v i).eval ρ) (X.eval ρ)) := rr_rel_sat_l I
    (R := R.eval ρ) ⟨(v 0).eval ρ, h 0⟩ φ closed
    ⟨fun i => ⟨(v i).eval ρ, h i⟩, fun _ => ⟨(v 0).eval ρ, h 0⟩⟩ ρ X R v rfl rfl (fun _ => rfl)
  exact ⟨fun ⟨h, valid⟩ => ⟨h, (read h).mp valid⟩, fun ⟨h, valid⟩ => ⟨h, (read h).mpr valid⟩⟩

theorem Rr_truth_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    {n} {φ : Formula 1 (n+1)} (closed : φ.FreeClosed) {v w : Fin (n+1) → M.Domain}
    (h : Rr_truth_d I X R φ v) (images : ∀ i, M.PairMember I (v i) (w i) j) : Rr_truth_d I Y S φ w := by
  obtain ⟨hv, valid⟩ := h
  have hw i := map.1.1.output_mem_of_pairMember (images i)
  exact ⟨hw, (smap_source_l I hZF hω mx my map φ closed
    ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨v 0, hv 0⟩⟩
    ⟨fun i => ⟨w i, hw i⟩, fun _ => ⟨w 0, hw 0⟩⟩ images).mp valid⟩

theorem rr_truth_mem_l {c X R : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    {n} (φ : Formula 1 (n+1)) (delta : φ.IsDelta0) (v : Fin (n+1) → M.Domain) :
    Rr_truth_d I X R φ v ↔ (∀ i, M.mem (v i) X) ∧
      Formula.satisfies (⟨v, fun _ => v 0⟩ : Env M (n+1)) φ := by
  have read (hv : ∀ i, M.mem (v i) X) :=
    (smem_formula_l I model ⟨⟨v 0, hv 0⟩⟩ φ
      ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨v 0, hv 0⟩⟩).symm.trans
      (rt_model_delta_l trans ⟨⟨v 0, hv 0⟩⟩ delta _)
  exact ⟨fun ⟨hv, h⟩ => ⟨hv, (read hv).mp h⟩, fun ⟨hv, h⟩ => ⟨hv, (read hv).mpr h⟩⟩

abbrev Rf_record_d {n} (X R : M.Domain) (φ : Formula 1 (n+1)) (C r : M.Domain) : Prop :=
  Rr_truth_d I X R (rt_record_in0_m φ) (Fin.cases C (fun _ => r))

abbrev Rf_tuple_d {n} (X R : M.Domain) (v : Fin (n+1) → M.Domain) (r : M.Domain) : Prop :=
  Rr_truth_d I X R (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) (Fin.cases r v)

def rf_record_m {d n} (φ : Formula 1 (n+1)) (X R C r : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (rt_record_in0_m φ) X R (Fin.cases C (fun _ => r))

def rf_tuple_m {d n} (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) X R (Fin.cases r v)

@[simp] theorem rf_record_closed_l {d n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R C r : Term d) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hC : C.freeSupport = []) (hr : r.freeSupport = []) : (rf_record_m (𝒞 := 𝒞) φ X R C r).FreeClosed :=
  rr_truth_closed_l _ (rt_record_in0_closed_l φ closed) X R _ hX hR (Fin.cases hC (fun _ => hr))

@[simp] theorem rf_tuple_closed_l {d n} (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (hr : r.freeSupport = []) : (rf_tuple_m (𝒞 := 𝒞) X R v r).FreeClosed :=
  rr_truth_closed_l _ (rt_tuple_closed_l _ _ (fun _ => rfl) rfl) X R _ hX hR (Fin.cases hr hv)

theorem rf_record_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) (X R C r : Term d) :
    Formula.satisfies ρ (rf_record_m (𝒞 := 𝒞) φ X R C r) ↔
      Rf_record_d I (X.eval ρ) (R.eval ρ) φ (C.eval ρ) (r.eval ρ) := by
  rw [rf_record_m, rr_truth_sat_l I ρ _ (rt_record_in0_closed_l φ closed)]
  have eq : (fun i : Fin 2 => ((Fin.cases C (fun _ => r) : Fin 2 → Term d) i).eval ρ) =
      Fin.cases (C.eval ρ) (fun _ => r.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq]

theorem rf_tuple_sat_l {d n} (ρ : Env M d) (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d) :
    Formula.satisfies ρ (rf_tuple_m (𝒞 := 𝒞) X R v r) ↔
      Rf_tuple_d I (X.eval ρ) (R.eval ρ) (fun i => (v i).eval ρ) (r.eval ρ) := by
  rw [rf_tuple_m, rr_truth_sat_l I ρ _ (rt_tuple_closed_l _ _ (fun _ => rfl) rfl)]
  have eq : (fun i : Fin (n+2) => ((Fin.cases r v : Fin (n+2) → Term d) i).eval ρ) =
      Fin.cases (r.eval ρ) (fun i => (v i).eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq]

theorem rf_record_mem_l {c X R C r : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    {n} (φ : Formula 1 (n+1)) :
    Rf_record_d I X R φ C r ↔ M.mem C X ∧ Rt_record_in_d φ C r := by
  rw [Rf_record_d, rr_truth_mem_l I trans model _ (rt_record_in0_delta_l φ)]
  exact ⟨fun ⟨mem, h⟩ => ⟨mem 0, h⟩,
    fun ⟨mem, h⟩ => ⟨Fin.cases mem (fun _ => trans C mem r h.member_l), h⟩⟩

theorem rf_tuple_mem_l (hE : Extensional M) {c X R r : M.Domain} (trans : M.TransitiveSet X)
    (model : Smem_d I c X R) {n} (v : Fin (n+1) → M.Domain) :
    Rf_tuple_d I X R v r ↔ M.mem r X ∧ Rt_tuple_d v r := by
  let t : Fin (n+2) → M.Domain := Fin.cases r v
  have read (hv : ∀ i, M.mem (t i) X) :
      Formula.satisfies (⟨fun i => ⟨t i, hv i⟩, fun _ => ⟨t 0, hv 0⟩⟩ :
        Env (smdl_structure_l I (X := X) (R := R) model.1.2.1) (n+2))
          (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) ↔ Rt_tuple_d v r := by
    let nx : Nonempty {x // M.mem x X} := ⟨⟨r, hv 0⟩⟩
    let ρ : Env (rt_model_l X nx) (n+2) := ⟨fun i => ⟨t i, hv i⟩, fun _ => ⟨t 0, hv 0⟩⟩
    exact (smem_formula_l I model nx (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) ρ).symm.trans
      ((rt_tuple_sat_l (rt_model_ext_l hE trans nx) ρ _ _).trans
        (rt_tuple_source_l hE trans nx (fun i => ρ.bound i.succ) (ρ.bound 0)))
  exact ⟨fun ⟨hv, h⟩ => ⟨hv 0, (read hv).mp h⟩, fun ⟨hr, h⟩ =>
    ⟨Fin.cases hr (Internal.Rt_tuple_d.members_l h trans hr),
      (read (Fin.cases hr (Internal.Rt_tuple_d.members_l h trans hr))).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal
