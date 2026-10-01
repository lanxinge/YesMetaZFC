import YesMetaZFC.SetTheory.InnerModel.Separation.Atomic
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 原 Project 公式的集合内真值表

每个赋值末尾保留一个哑坐标，使零元公式也有正元数编码；该坐标只提供实际
自由赋值，不改变原公式。表的存在性由公式结构归纳和有限基逐项给出。
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

def rt_env_l {U : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x U}) {n} (e : Rt_env U n) :
    Env (rt_model_l U hn) n := ⟨fun i => e i.castSucc, fun _ => e (Fin.last n)⟩

theorem rt_env_push_l {U : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x U}) {n}
    (e : Rt_env U n) (x : (rt_model_l U hn).Domain) :
    rt_env_l hn (Fin.cases x e) = (rt_env_l hn e).push x := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩

theorem rt_term_l {n} (t : Term n) (ht : t.freeSupport = []) : ∃ i, t = .bound i := by
  cases t with
  | bound i => exact ⟨i, rfl⟩
  | free i => cases ht

theorem rt_formula_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (hu : M.TransitiveSet U) (hn : Nonempty {x : M.Domain // M.mem x U})
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) :
    ∃ R, M.mem R C ∧ Rt_table_d U (fun e => Formula.satisfies (rt_env_l hn e) φ) R := by
  induction φ <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case truth n =>
    simpa only [Formula.satisfies_truth_iff] using rt_power_l hKP hC hU n
  case falsum n =>
    obtain ⟨R, hRC, hR⟩ := rt_power_l hKP hC hU n
    simpa only [Formula.satisfies_falsum_iff, not_true_eq_false] using rt_neg_l hKP hC hU hRC hR
  case mem n x y =>
    obtain ⟨i, rfl⟩ := rt_term_l x hφ.1
    obtain ⟨j, rfl⟩ := rt_term_l y hφ.2
    simpa only [Formula.satisfies_mem_iff] using! rt_mem_l hKP hC hU hu i.castSucc j.castSucc
  case atom n s hs ts =>
    obtain ⟨i, hi⟩ := rt_term_l (ts.get 0) (hφ 0)
    obtain ⟨j, hj⟩ := rt_term_l (ts.get 1) (hφ 1)
    cases s with
    | subset =>
      simpa only [Formula.satisfies_atom_subset_iff, hi, hj, Term.eval_bound] using!
        rt_subset_l hKP hC hU i.castSucc j.castSucc
    | extensionalEq =>
      obtain ⟨R, hRC, hR⟩ := rt_eq_l hKP hC hU hu i.castSucc j.castSucc
      refine ⟨R, hRC, hR.congr_l fun e => ?_⟩
      simp only [Formula.satisfies_atom_extensionalEq_iff, hi, hj, Term.eval_bound]
      change (e i.castSucc = e j.castSucc) ↔ ∀ z : (rt_model_l U hn).Domain,
        M.mem z.val (e i.castSucc).val ↔ M.mem z.val (e j.castSucc).val
      exact ⟨fun he => he ▸ (fun _ => Iff.rfl), (rt_model_ext_l hKP.1 hu hn).eq_of_same_members _ _⟩
  case neg φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ
    simpa only [Formula.satisfies_neg_iff] using rt_neg_l hKP hC hU hRC hR
  case conj φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1
    obtain ⟨S, hSC, hS⟩ := jh hφ.2
    simpa only [Formula.satisfies_conj_iff] using rt_and_l hKP hC hRC hSC hR hS
  case disj φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1
    obtain ⟨S, hSC, hS⟩ := jh hφ.2
    simpa only [Formula.satisfies_disj_iff] using rt_or_l hKP hC hRC hSC hR hS
  case imp φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1
    obtain ⟨S, hSC, hS⟩ := jh hφ.2
    simpa only [Formula.satisfies_imp_iff] using rt_imp_l hKP hC hU hRC hSC hR hS
  case iff φ ψ ih jh =>
    obtain ⟨R, hRC, hR⟩ := ih hφ.1
    obtain ⟨S, hSC, hS⟩ := jh hφ.2
    simpa only [Formula.satisfies_iff_iff] using rt_iff_l hKP hC hU hRC hSC hR hS
  case forallE φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ
    obtain ⟨S, hSC, hS⟩ := rt_forall_l hKP hC hU hRC hR
    refine ⟨S, hSC, hS.congr_l fun e => ?_⟩
    rw [Formula.satisfies_forall_iff]
    exact forall_congr' fun x => Iff.of_eq (congrArg (fun ρ => Formula.satisfies ρ φ) (rt_env_push_l hn e x))
  case existsE φ ih =>
    obtain ⟨R, hRC, hR⟩ := ih hφ
    obtain ⟨S, hSC, hS⟩ := rt_exists_l hKP hC hRC hR
    refine ⟨S, hSC, hS.congr_l fun e => ?_⟩
    rw [Formula.satisfies_exists_iff]
    exact exists_congr fun x => Iff.of_eq (congrArg (fun ρ => Formula.satisfies ρ φ) (rt_env_push_l hn e x))

theorem rt_model_delta_l {U : M.Domain} (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) {n} {φ : Formula 1 n}
    (hφ : φ.IsDelta0) (ρ : Env (rt_model_l U hn) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l Subtype.val ρ) φ :=
  delta0_image_l (M := rt_model_l U hn) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun a y => ⟨fun h => ⟨⟨y, hu a.val a.property y h⟩, h, rfl⟩,
      fun ⟨_, hx, he⟩ => he ▸ hx⟩) hφ ρ

end YesMetaZFC.SetTheory.InnerModel
