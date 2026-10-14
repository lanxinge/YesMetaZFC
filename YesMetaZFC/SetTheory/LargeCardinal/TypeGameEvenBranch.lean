import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunUnion
import YesMetaZFC.SetTheory.LargeCardinal.IterationBranch

/-! # 实际偶数节点列产生共尾分支

分支由各当前偶数节点的前驱组成。任意两个阶段有共同后继；偶数边保持
这些前驱，而轮号小于树长保证这条分支在内部 ω 中共尾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_even_d (f T x : M.Domain) : Prop := ∃ q : Fin 64 → M.Domain,
  ∃ i s, Rd_entry_d i s f ∧ Rt_tuple_d q s ∧ Rd_entry_d x (q 7) T

private def tg_even_body_m : Formula 1 67 := .existsE (.existsE
  (.conj (rd_entry0_m (.bound 1) .newest (.bound 66))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 3).succ.succ) .newest)
      (rd_entry0_m (.bound 68) (.bound 9) (.bound 67)))))
def tg_even0_m : Formula 1 3 := rt_exists_m 64 tg_even_body_m

theorem tg_even0_closed_l : tg_even0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  simp -implicitDefEqProofs [tg_even_body_m, Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_even0_sat_l (hE : Extensional M) (η : Env M 3) :
    Formula.satisfies η tg_even0_m ↔ Tg_even_d (η.bound 0) (η.bound 1) (η.bound 2) := by
  rw [tg_even0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  have new (i : Fin 64) : (rt_push_d η 64 q).bound (i.castAdd 3) = q i := rt_push_new_l η q i
  simp only [tg_even_body_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rt_tuple_sat_l hE, Term.eval_bound]
  change (∃ i s, Rd_entry_d i s ((rt_push_d η 64 q).bound 64) ∧
    Rt_tuple_d (fun j => (rt_push_d η 64 q).bound (j.castAdd 3)) s ∧
    Rd_entry_d ((rt_push_d η 64 q).bound 66) ((rt_push_d η 64 q).bound 7) ((rt_push_d η 64 q).bound 65)) ↔ _
  simp only [new]
  rw [show (rt_push_d η 64 q).bound 64 = η.bound 0 from rt_push_old_l η q 0,
    show (rt_push_d η 64 q).bound 65 = η.bound 1 from rt_push_old_l η q 1,
    show (rt_push_d η 64 q).bound 66 = η.bound 2 from rt_push_old_l η q 2,
    show (rt_push_d η 64 q).bound 7 = q 7 from new 7]

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.even_branch_l {ω c o C γ Z A D f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x) :
    ∃ B, It_branch_d ω (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x := by
  let φ : UnarySchema 2 := {
    body := tg_even0_m.bind (fun i => [.bound 1, .bound 2, .newest].get i)
    freeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _).mpr tg_even0_closed_l }
  let η : Env M 2 := ⟨Fin.cases f (fun _ => U 0), fun _ => f⟩
  have sat x : φ.denote η x ↔ Tg_even_d f (U 0) x := by
    rw [UnarySchema.denote, Formula.satisfies_bind, tg_even0_sat_l hZF.1]; rfl
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF φ η ω
  have bound {x} (hx : Tg_even_d f (U 0) x) : M.mem x ω := by
    obtain ⟨v, i, s, hs, code, edge⟩ := hx
    exact (tree.tree.diagram.order.bound x (v 7) edge).1
  have iff x : M.mem x B ↔ Tg_even_d f (U 0) x := (bs x).trans
    ((and_congr_right fun _ => sat x).trans ⟨And.right, fun hx => ⟨bound hx, hx⟩⟩)
  have keeps {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {x y} (xy : Rd_entry_d x y (v 8)) : Rd_entry_d x y (U 0) := by
    obtain ⟨p, pair, hp⟩ := xy
    exact ⟨p, pair, (columns 0 p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  refine ⟨B, ⟨fun x hx => bound ((iff x).mp hx), ?_, ?_, ?_⟩, iff⟩
  · intro x y hx hy
    obtain ⟨v, i, s, hs, ps, xv⟩ := (iff x).mp hx
    obtain ⟨w, j, t, ht, pt, yw⟩ := (iff y).mp hy
    obtain ⟨k, r, u, hr, pr, vu, wu⟩ := h.merge_l hZF tree.tree.omega hs ht ps pt
    have vrun := (h.read_l hZF hs ps).1
    have wrun := (h.read_l hZF ht pt).1
    have vhead := keeps hr pr (vu.2.2.2 (v 7) (vrun.tree.tree.diagram.order.refl _ vrun.successor.predecessor_mem))
    have whead := keeps hr pr (wu.2.2.2 (w 7) (wrun.tree.tree.diagram.order.refl _ wrun.successor.predecessor_mem))
    exact tree.tree.diagram.order.chain x y (u 7)
      (tree.tree.diagram.order.trans x (v 7) (u 7) xv vhead) (tree.tree.diagram.order.trans y (w 7) (u 7) yw whead)
  · intro x y xy hy
    obtain ⟨v, i, s, hs, ps, yv⟩ := (iff y).mp hy
    exact (iff x).mpr ⟨v, i, s, hs, ps, tree.tree.diagram.order.trans x y (v 7) xy yv⟩
  · intro i hi
    obtain ⟨s, _, hs⟩ := h.function.2.1 i hi
    obtain ⟨_, _, v, ps, _⟩ := h.rows i s hs
    obtain ⟨run, span⟩ := h.read_l hZF hs ps
    refine ⟨v 7, (iff _).mpr ⟨v, i, s, hs, ps, tree.tree.diagram.order.refl _ run.finite⟩, ?_⟩
    exact ((run.successor i).mp span).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members i _ eq))

end YesMetaZFC.SetTheory.LargeCardinal
