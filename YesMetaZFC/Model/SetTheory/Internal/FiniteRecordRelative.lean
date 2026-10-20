import YesMetaZFC.Model.SetTheory.Internal.FiniteRecord
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 拥有秩层中的实际有限记录

记录的坐标与证书均处于同一给定集合中。原公式相对化后是背景的有界公式，
可直接放入内部历史谓词，并沿实际初等图搬运。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rt_record_in0_m {n} (φ : Formula 1 (n+1)) : Formula 1 2 :=
  .conj (.mem (.bound 1) (.bound 0))
    (lr_rel_m (rt_record_m (d := 1) φ .newest) (.bound 0) (fun i => .bound i.succ))

def rt_record_in_m {d n} (φ : Formula 1 (n+1)) (C r : Term d) : Formula 1 d :=
  (rt_record_in0_m φ).bind (Fin.cases C (fun _ => r))

def Rt_record_in_d {n} (φ : Formula 1 (n+1)) (C r : M.Domain) : Prop :=
  Formula.satisfies (⟨Fin.cases C (fun _ => r), fun _ => C⟩ : Env M 2) (rt_record_in0_m φ)

theorem rt_record_in0_closed_l {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) :
    (rt_record_in0_m φ).FreeClosed :=
  ⟨⟨rfl, rfl⟩, lr_rel_closed_l _ (rt_record_closed_l φ _ closed rfl) _ _ rfl (fun _ => rfl)⟩

theorem rt_record_in0_delta_l {n} (φ : Formula 1 (n+1)) : (rt_record_in0_m φ).IsDelta0 :=
  .conj (.mem ..) (lr_rel_delta_l ..)

theorem rt_record_in_closed_l {d n} (φ : Formula 1 (n+1)) (C r : Term d)
    (closed : φ.FreeClosed) (hC : C.freeSupport = []) (hr : r.freeSupport = []) :
    (rt_record_in_m φ C r).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hC (fun _ => hr)) _).mpr
    (rt_record_in0_closed_l φ closed)

theorem rt_record_in_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (C r : Term d)
    (closed : φ.FreeClosed) : Formula.satisfies ρ (rt_record_in_m φ C r) ↔
      Rt_record_in_d φ (C.eval ρ) (r.eval ρ) := by
  rw [rt_record_in_m, Formula.satisfies_bind]
  exact Formula.closed_env_l _ (rt_record_in0_closed_l φ closed)
    (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

theorem Rt_record_in_d.member_l {n} {φ : Formula 1 (n+1)} {C r : M.Domain}
    (h : Rt_record_in_d φ C r) : M.mem r C := ((Formula.satisfies_conj_iff ..).mp h).1

variable (hE : Extensional M)
include hE

theorem rt_record_in_read_l {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) {C r : M.Domain}
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) : Rt_record_in_d φ C r ↔
    M.mem r C ∧ ∃ v : Fin (n+1) → (rt_model_l C nc).Domain, Rt_tuple_d (fun i => (v i).val) r ∧
      Formula.satisfies (⟨v, fun _ => v 0⟩ : Env (rt_model_l C nc) (n+1)) φ := by
  constructor
  · intro h
    let a : (rt_model_l C nc).Domain := ⟨r, h.member_l⟩
    let ρ : Env (rt_model_l C nc) 1 := ⟨fun _ => a, fun _ => a⟩
    have valid := (sc_relative_sat_l trans nc (rt_record_m φ .newest)
      (rt_record_closed_l _ _ closed rfl) ρ _ (.bound 0) (fun i => .bound i.succ) rfl (fun _ => rfl)).mp
      ((Formula.satisfies_conj_iff ..).mp h).2
    obtain ⟨v, tuple, valid⟩ := (rt_record_sat_l (rt_model_ext_l hE trans nc) ρ φ .newest closed).mp valid
    exact ⟨h.member_l, v, (rt_tuple_source_l hE trans nc v a).mp tuple,
      (Formula.closed_env_l φ closed (ρ := ⟨v, ρ.free⟩) (η := ⟨v, fun _ => v 0⟩) rfl).mp valid⟩
  · rintro ⟨hr, v, tuple, valid⟩
    let a : (rt_model_l C nc).Domain := ⟨r, hr⟩
    let ρ : Env (rt_model_l C nc) 1 := ⟨fun _ => a, fun _ => a⟩
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, (sc_relative_sat_l trans nc (rt_record_m φ .newest)
      (rt_record_closed_l _ _ closed rfl) ρ _ (.bound 0) (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr ?_⟩
    exact (rt_record_sat_l (rt_model_ext_l hE trans nc) ρ φ .newest closed).mpr
      ⟨v, (rt_tuple_source_l hE trans nc v a).mpr tuple,
        (Formula.closed_env_l φ closed (ρ := ⟨v, fun _ => v 0⟩) (η := ⟨v, ρ.free⟩) rfl).mp valid⟩

/-- 固定有限记录只需要配对闭包，与整个工作源的超幂性质无关。 -/
theorem rt_record_in_save_l {n C} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (trans : M.TransitiveSet C)
    (pair : ∀ a b, M.mem a C → M.mem b C → ∃ p, M.mem p C ∧ Pair_d M p a b)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) (n+1)) (valid : Formula.satisfies ρ φ) :
    ∃ r, Rt_record_in_d φ C r ∧ Rt_tuple_d (fun i => (ρ.bound i).val) r := by
  have tuple {k} (v : Fin (k+1) → (rt_model_l C nc).Domain) :
      ∃ r, M.mem r C ∧ Rt_tuple_d (fun i => (v i).val) r := by
    induction k with
    | zero => exact ⟨(v 0).val, (v 0).property, rfl⟩
    | succ k ih =>
      obtain ⟨r, hr, tail⟩ := ih (fun i => v i.succ)
      let r₀ : (rt_model_l C nc).Domain := ⟨r, hr⟩
      obtain ⟨q, code⟩ := (rt_pair_l trans nc hE pair).total (v 0) r₀
      exact ⟨q.val, q.property, (rt_tuple_source_l hE trans nc v q).mp ⟨r₀, code,
        (rt_tuple_source_l hE trans nc (fun i => v i.succ) r₀).mpr tail⟩⟩
  obtain ⟨r, hr, code⟩ := tuple ρ.bound
  exact ⟨r, (rt_record_in_read_l hE φ closed trans nc).mpr
    ⟨hr, ρ.bound, code, (Formula.closed_env_l φ closed
      (ρ := ρ) (η := ⟨ρ.bound, fun _ => ρ.bound 0⟩) rfl).mp valid⟩, code⟩

end YesMetaZFC.SetTheory.Internal
