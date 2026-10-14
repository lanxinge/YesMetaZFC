import YesMetaZFC.Model.SetTheory.Internal.FiniteRecord
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 固定元数记录列的实际坐标函数

按原元组码读取坐标；函数性来自元组唯一性。替代收集的每一列仍使用
同一内部指标域，语法元数不代替对象模型中的时间递归。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Rt_coord_d {n} (a : Fin (n+1)) (r x : M.Domain) : Prop :=
  ∃ v : Fin (n+1) → M.Domain, Rt_tuple_d v r ∧ v a = x

def rt_coord0_m {n} (a : Fin (n+1)) : Formula 1 2 := rt_exists_m (n+1) (.conj
  (rt_tuple_m (fun i : Fin (n+1) => .bound ⟨i.val, by omega⟩) (.bound ⟨n+1, by omega⟩))
  (Formula.extensionalEq (.bound ⟨a.val, by omega⟩) (.bound ⟨n+2, by omega⟩)))

theorem rt_coord0_closed_l {n} (a : Fin (n+1)) : (rt_coord0_m a).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, (Formula.extensionalEq_freeClosed_iff ..).mpr ⟨rfl, rfl⟩⟩

theorem rt_coord0_sat_l (hE : Extensional M) {n} (a : Fin (n+1)) (ρ : Env M 2) :
    Formula.satisfies ρ (rt_coord0_m a) ↔ Rt_coord_d a (ρ.bound 0) (ρ.bound 1) := by
  rw [rt_coord0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Term.eval_bound]
  have new (i : Fin (n+1)) : (rt_push_d ρ (n+1) v).bound ⟨i.val, by omega⟩ = v i := rt_push_new_l ρ v i
  rw [show (rt_push_d ρ (n+1) v).bound ⟨n+1, by omega⟩ = ρ.bound 0 from rt_push_old_l ρ v 0,
    show (rt_push_d ρ (n+1) v).bound ⟨n+2, by omega⟩ = ρ.bound 1 from rt_push_old_l ρ v 1,
    new a, show (fun i : Fin (n+1) => (rt_push_d ρ (n+1) v).bound ⟨i.val, by omega⟩) = v from funext new]

def rt_coord_m {d n} (a : Fin (n+1)) (r x : Term d) : Formula 1 d :=
  (rt_coord0_m a).bind (Fin.cases r (fun _ => x))

@[simp] theorem rt_coord_closed_l {d n} (a : Fin (n+1)) (r x : Term d)
    (hr : r.freeSupport = []) (hx : x.freeSupport = []) : (rt_coord_m a r x).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hr (fun _ => hx)) _).mpr (rt_coord0_closed_l a)

theorem rt_coord_sat_l (hE : Extensional M) {d n} (a : Fin (n+1)) (ρ : Env M d) (r x : Term d) :
    Formula.satisfies ρ (rt_coord_m a r x) ↔ Rt_coord_d a (r.eval ρ) (x.eval ρ) := by
  rw [rt_coord_m, Formula.satisfies_bind, rt_coord0_sat_l hE]; rfl

theorem rt_coordinate_l (hZF : M.Models ZF) {A D F N : M.Domain} {k : Nat} (a : Fin (k+1))
    (fn : Fn0_d A D F) (rows : ∀ i r, Rd_entry_d i r F → ∃ v : Fin (k+1) → M.Domain, Rt_tuple_d v r)
    (bound : ∀ i r (v : Fin (k+1) → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → M.mem (v a) N) :
    ∃ G, Fn0_d A N G ∧
      ∀ i x, Rd_entry_d i x G ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d a r x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (rt_coord_m a .newest (.bound 1))) }
  have sat i x : φ.denote ρ i x ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d a r x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rt_coord_sat_l hZF.1]; rfl
  obtain ⟨G, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := N) (by
    intro i hi
    obtain ⟨r, _, hr⟩ := fn.2.1 i hi
    obtain ⟨v, code⟩ := rows i r hr
    exact ⟨v a, (sat i (v a)).mpr ⟨r, hr, v, code, rfl⟩⟩) (by
    intro i _ x y hx hy
    obtain ⟨r, hr, v, code, eq⟩ := (sat i x).mp hx
    obtain ⟨s, hs, w, pack, eq'⟩ := (sat i y).mp hy
    have rs := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i s r hs hr
    subst s
    exact eq.symm.trans ((congrFun (rt_tuple_inj_l code pack) a).trans eq')) (by
    intro i x _ hx
    obtain ⟨r, hr, v, code, eq⟩ := (sat i x).mp hx
    exact eq ▸ bound i r v hr code)
  refine ⟨G, fn0_of_function_l (ZF.modelsKP hZF) gf, fun i x => (gs i x).trans ?_⟩
  exact (and_congr_right fun _ => sat i x).trans ⟨And.right, fun h =>
    ⟨h.elim fun r h => (fn.bound_l h.1).1, h⟩⟩

end YesMetaZFC.SetTheory.Internal
