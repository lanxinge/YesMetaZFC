import YesMetaZFC.SetTheory.LargeCardinal.TypeGameEvenBranch
import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection

/-! # 同一分支锥中的实际历史像列

记录坐标沿所属偶数节点的真实锥映射进入目标。函数性来自原记录和锥图
的唯一性；替代构造整条内部序列，不假定目标模型满足替代。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_limit_value_d (a : Fin 46) (f P i x : M.Domain) : Prop := ∃ v : Fin 64 → M.Domain,
  ∃ s j, Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d (v 7) j P ∧ Rd_entry_d (v (Fin.natAdd 18 a)) x j

private def tg_limit_value_body_m (a : Fin 46) : Formula 1 68 := .existsE (.existsE
  (.conj (rd_entry0_m (.bound 68) (.bound 1) (.bound 66))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 4).succ.succ) (.bound 1))
      (.conj (rd_entry0_m (.bound 9) .newest (.bound 67))
        (rd_entry0_m (.bound ((Fin.natAdd 18 a).castAdd 4).succ.succ) (.bound 69) .newest)))))
def tg_limit_value0_m (a : Fin 46) : Formula 1 4 := rt_exists_m 64 (tg_limit_value_body_m a)

theorem tg_limit_value0_closed_l (a : Fin 46) : (tg_limit_value0_m a).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  simp -implicitDefEqProofs [tg_limit_value_body_m, Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_limit_value0_sat_l (hE : Extensional M) (a : Fin 46) (η : Env M 4) :
    Formula.satisfies η (tg_limit_value0_m a) ↔ Tg_limit_value_d a (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) := by
  rw [tg_limit_value0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  have new (i : Fin 64) : (rt_push_d η 64 v).bound (i.castAdd 4) = v i := rt_push_new_l η v i
  simp only [tg_limit_value_body_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rt_tuple_sat_l hE, Term.eval_bound]
  change (∃ s j, Rd_entry_d ((rt_push_d η 64 v).bound 66) s ((rt_push_d η 64 v).bound 64) ∧
    Rt_tuple_d (fun k => (rt_push_d η 64 v).bound (k.castAdd 4)) s ∧
    Rd_entry_d ((rt_push_d η 64 v).bound 7) j ((rt_push_d η 64 v).bound 65) ∧
    Rd_entry_d ((rt_push_d η 64 v).bound ((Fin.natAdd 18 a).castAdd 4)) ((rt_push_d η 64 v).bound 67) j) ↔ _
  simp only [new]
  rw [show (rt_push_d η 64 v).bound 64 = η.bound 0 from rt_push_old_l η v 0,
    show (rt_push_d η 64 v).bound 65 = η.bound 1 from rt_push_old_l η v 1,
    show (rt_push_d η 64 v).bound 66 = η.bound 2 from rt_push_old_l η v 2,
    show (rt_push_d η 64 v).bound 67 = η.bound 3 from rt_push_old_l η v 3,
    show (rt_push_d η 64 v).bound 7 = v 7 from new 7]

def tg_limit_value_m {d} (a : Fin 46) (f P i x : Term d) : Formula 1 d :=
  (tg_limit_value0_m a).bind (fun j => [f,P,i,x].get j)
@[simp] theorem tg_limit_value_closed_l {d} (a : Fin 46) (f P i x : Term d)
    (hf : f.freeSupport = []) (hP : P.freeSupport = []) (hi : i.freeSupport = []) (hx : x.freeSupport = []) :
    (tg_limit_value_m a f P i x).FreeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases hf (Fin.cases hP (Fin.cases hi (Fin.cases hx (fun j => Fin.elim0 j))))) _).mpr (tg_limit_value0_closed_l a)

theorem tg_limit_value_sat_l (hE : Extensional M) {d} (a : Fin 46) (η : Env M d) (f P i x : Term d) :
    Formula.satisfies η (tg_limit_value_m a f P i x) ↔ Tg_limit_value_d a (f.eval η) (P.eval η) (i.eval η) (x.eval η) := by
  rw [tg_limit_value_m, Formula.satisfies_bind, tg_limit_value0_sat_l hE]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.limit_values_l {ω c o C γ Z A D f B d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x)
    (cone : It_embedding_d hZF ω B (U 1) (U 2) d N W P) (a : Fin 46) :
    ∃ F, Fn0_d ω N F ∧ ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d a f P i x := by
  have node {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) : Rd_entry_d (v 7) (v 15) (U 1) := by
    obtain ⟨p, pair, hp⟩ := (h.read_l hZF hs code).1.node
    exact ⟨p, pair, (columns 1 p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  have map {i s j} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hj : Rd_entry_d (v 7) j P) :=
    cone.elementary (v 7) j (v 15) (v 0) (v 1) hj (node hs code) (h.read_l hZF hs code).1.model.1
  have total i (hi : M.mem i ω) : ∃ x, Tg_limit_value_d a f P i x := by
    obtain ⟨s, _, hs⟩ := h.function.2.1 i hi
    obtain ⟨_, _, v, code, _⟩ := h.rows i s hs
    have run := (h.read_l hZF hs code).1
    have hb := (branch (v 7)).mpr ⟨v, i, s, hs, code, tree.tree.diagram.order.refl _ run.finite⟩
    obtain ⟨j, hj⟩ := (cone.domain (v 7)).mp hb
    let nc : Nonempty {x // M.mem x (v 5)} := ⟨⟨ω, run.context.omega⟩⟩
    obtain ⟨ι, eq, _⟩ := run.read_l hZF nc
    have mem : M.mem (v (Fin.natAdd 18 a)) (v 0) := (eq a) ▸
      run.source.source.transitive _ run.context.member _ (ι.bound a).property
    obtain ⟨x, _, hx⟩ := (map hs code hj).1.1.2.2 _ mem
    exact ⟨x, v, s, j, hs, code, hj, hx⟩
  have unique i x y (hx : Tg_limit_value_d a f P i x) (hy : Tg_limit_value_d a f P i y) : x = y := by
    obtain ⟨v, s, j, hs, ps, hj, hx⟩ := hx
    obtain ⟨w, t, k, ht, pt, hk, hy⟩ := hy
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 i t s ht hs
    subst t
    have eq := rt_tuple_inj_l pt ps
    subst w
    have eq := cone.function.2 (v 7) k j hk hj
    subst k
    exact (map hs ps hj).1.1.1.2 _ x y hx hy
  let η : Env M 2 := ⟨Fin.cases f (fun _ => P), fun _ => f⟩
  let φ : BinarySchema 2 := { body := tg_limit_value_m a (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat i x : φ.denote η i x ↔ Tg_limit_value_d a f P i x := tg_limit_value_sat_l hZF.1 ..
  obtain ⟨F, ff, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η
    (fun i hi => (total i hi).imp fun x hx => (sat i x).mpr hx)
    (fun i _ x y hx hy => unique i x y ((sat i x).mp hx) ((sat i y).mp hy)) (by
      intro i x _ hx
      obtain ⟨v, s, j, hs, code, hj, hx⟩ := (sat i x).mp hx
      exact (map hs code hj).1.1.output_mem_of_pairMember hx)
  refine ⟨F, fn0_of_function_l (ZF.modelsKP hZF) ff, fun i x => (fs i x).trans ?_⟩
  exact (and_congr_right fun _ => sat i x).trans ⟨And.right,
    fun hx => ⟨hx.elim fun _ hv => hv.elim fun _ hs => hs.elim fun _ hs => (h.function.bound_l hs.1).1, hx⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
