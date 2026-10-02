import YesMetaZFC.SetTheory.InnerModel.Separation.Atomic
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 原 Project 公式的集合内真值表

有限赋值通过坐标映射解释公式，允许重复、置换及哑坐标；零元公式也使用正元数
编码。自由闭合性保证哑坐标无关。表的存在性由公式结构归纳和有限基逐项给出。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rt_model_l (U : M.Domain) (hn : Nonempty {x : M.Domain // M.mem x U}) : Structure.{u} where
  Domain := {x : M.Domain // M.mem x U}
  nonempty := hn
  mem x y := M.mem x.val y.val

theorem rt_model_ext_l (hE : Extensional M) {U : M.Domain} (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) : Extensional (rt_model_l U hn) := by
  refine ⟨fun a b h => Subtype.ext (hE.eq_of_same_members a.val b.val (fun x => ?_))⟩
  exact ⟨fun hx => (h ⟨x, hu a.val a.property x hx⟩).mp hx,
    fun hx => (h ⟨x, hu b.val b.property x hx⟩).mpr hx⟩

def rt_env_l {U : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x U}) {m n}
    (f : Fin m → Fin (n + 1)) (e : Rt_env U n) : Env (rt_model_l U hn) m :=
  ⟨fun i => e (f i), fun _ => e 0⟩

theorem rt_env_push_l {U : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x U}) {m n}
    (f : Fin m → Fin (n + 1)) (e : Rt_env U n) (x : (rt_model_l U hn).Domain)
    (φ : Formula 1 (m + 1)) (hφ : φ.FreeClosed) :
    Formula.satisfies (rt_env_l hn (Fin.cases 0 (fun i => (f i).succ)) (Fin.cases x e)) φ ↔
      Formula.satisfies ((rt_env_l hn f e).push x) φ := by
  apply Formula.closed_env_l _ hφ
  exact funext (Fin.cases rfl (fun _ => rfl))

theorem rt_term_l {n} (t : Term n) (ht : t.freeSupport = []) : ∃ i, t = .bound i := by
  cases t with
  | bound i => exact ⟨i, rfl⟩
  | free i => cases ht

theorem rt_formula_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (hu : M.TransitiveSet U) (hn : Nonempty {x : M.Domain // M.mem x U})
    {m n} (φ : Formula 1 m) (hφ : φ.FreeClosed) (f : Fin m → Fin (n + 1)) :
    ∃ R, M.mem R C ∧ Rt_table_d U (fun e => Formula.satisfies (rt_env_l hn f e) φ) R := by
  induction φ generalizing n <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case truth m =>
    simpa only [Formula.satisfies_truth_iff] using rt_power_l hKP hC hU n
  case falsum m =>
    obtain ⟨R, hRC, hR⟩ := rt_power_l hKP hC hU n
    simpa only [Formula.satisfies_falsum_iff, not_true_eq_false] using rt_neg_l hKP hC hU hRC hR
  case mem m x y =>
    obtain ⟨i, rfl⟩ := rt_term_l x hφ.1
    obtain ⟨j, rfl⟩ := rt_term_l y hφ.2
    simpa only [Formula.satisfies_mem_iff] using! rt_mem_l hKP hC hU hu (f i) (f j)
  case atom m s hs ts =>
    obtain ⟨i, hi⟩ := rt_term_l (ts.get 0) (hφ 0)
    obtain ⟨j, hj⟩ := rt_term_l (ts.get 1) (hφ 1)
    cases s with
    | subset =>
      simpa only [Formula.satisfies_atom_subset_iff, hi, hj, Term.eval_bound] using!
        rt_subset_l hKP hC hU (f i) (f j)
    | extensionalEq =>
      obtain ⟨R, hRC, hR⟩ := rt_eq_l hKP hC hU hu (f i) (f j)
      refine ⟨R, hRC, hR.congr_l fun e => ?_⟩
      simp only [Formula.satisfies_atom_extensionalEq_iff, hi, hj, Term.eval_bound]
      change (e (f i) = e (f j)) ↔ ∀ z : (rt_model_l U hn).Domain,
        M.mem z.val (e (f i)).val ↔ M.mem z.val (e (f j)).val
      exact ⟨fun he => he ▸ (fun _ => Iff.rfl), (rt_model_ext_l hKP.1 hu hn).eq_of_same_members _ _⟩
  case neg φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ f
    simpa only [Formula.satisfies_neg_iff] using rt_neg_l hKP hC hU hRC hR
  case conj φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1 f
    obtain ⟨S, hSC, hS⟩ := jh hφ.2 f
    simpa only [Formula.satisfies_conj_iff] using rt_and_l hKP hC hRC hSC hR hS
  case disj φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1 f
    obtain ⟨S, hSC, hS⟩ := jh hφ.2 f
    simpa only [Formula.satisfies_disj_iff] using rt_or_l hKP hC hRC hSC hR hS
  case imp φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1 f
    obtain ⟨S, hSC, hS⟩ := jh hφ.2 f
    simpa only [Formula.satisfies_imp_iff] using rt_imp_l hKP hC hU hRC hSC hR hS
  case iff φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1 f
    obtain ⟨S, hSC, hS⟩ := jh hφ.2 f
    simpa only [Formula.satisfies_iff_iff] using rt_iff_l hKP hC hU hRC hSC hR hS
  case forallE φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ (Fin.cases 0 (fun i => (f i).succ))
    obtain ⟨S, hSC, hS⟩ := rt_forall_l hKP hC hU hRC hR
    refine ⟨S, hSC, hS.congr_l fun e => ?_⟩
    rw [Formula.satisfies_forall_iff]
    exact forall_congr' fun x => rt_env_push_l hn f e x φ hφ
  case existsE φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ (Fin.cases 0 (fun i => (f i).succ))
    obtain ⟨S, hSC, hS⟩ := rt_exists_l hKP hC hRC hR
    refine ⟨S, hSC, hS.congr_l fun e => ?_⟩
    rw [Formula.satisfies_exists_iff]
    exact exists_congr fun x => rt_env_push_l hn f e x φ hφ

theorem rt_model_delta_l {U : M.Domain} (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) {n} {φ : Formula 1 n}
    (hφ : φ.IsDelta0) (ρ : Env (rt_model_l U hn) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l Subtype.val ρ) φ :=
  delta0_image_l (M := rt_model_l U hn) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun a y => ⟨fun h => ⟨⟨y, hu a.val a.property y h⟩, h, rfl⟩,
      fun ⟨_, hx, he⟩ => he ▸ hx⟩) hφ ρ

theorem rt_delta_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (hu : M.TransitiveSet U) (hn : Nonempty {x : M.Domain // M.mem x U})
    {m n} (φ : Formula 1 m) (hφ : φ.FreeClosed) (hd : φ.IsDelta0) (f : Fin m → Fin (n + 1)) :
    ∃ R, M.mem R C ∧ Rt_table_d U
      (fun e => Formula.satisfies (⟨fun i => (e (f i)).val, fun _ => (e 0).val⟩ : Env M m) φ) R := by
  obtain ⟨R, hRC, hR⟩ := rt_formula_l hKP hC hU hu hn φ hφ f
  exact ⟨R, hRC, hR.congr_l fun e => rt_model_delta_l hu hn hd (rt_env_l hn f e)⟩

end YesMetaZFC.SetTheory.InnerModel
