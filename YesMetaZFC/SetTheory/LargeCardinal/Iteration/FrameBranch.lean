import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch

/-! # 共尾有限框架的当前节点枝

各当前节点的前驱取并成为分支。共同阶段保持前驱，长度后继和阶段共尾性给出分支共尾性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_even_d {n} (a : Fin (n+1)) (f T x : M.Domain) : Prop := ∃ v : Fin (n+1) → M.Domain,
  ∃ i s, Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d x (v a) T

def tg_even0_m {n} (a : Fin (n+1)) : Formula 1 3 :=
  let v : Fin (n+1) → Term ((n+1)+3) := fun i => .bound (i.castAdd 3)
  let p : Fin 3 → Term ((n+1)+3) := fun i => .bound (Fin.natAdd (n+1) i)
  rb_exists_m (n := n+1) (.existsE (.existsE
    (.conj (rd_entry0_m (.bound 1) .newest (p 0).weaken.weaken)
      (.conj (rt_tuple_m (fun i => (v i).weaken.weaken) .newest)
        (rd_entry0_m (p 2).weaken.weaken (v a).weaken.weaken (p 1).weaken.weaken)))))

theorem tg_even0_closed_l {n} (a : Fin (n+1)) : (tg_even0_m a).FreeClosed := by
  simp -implicitDefEqProofs [tg_even0_m,Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_even0_sat_l (hE : Extensional M) {n} (a : Fin (n+1)) (η : Env M 3) :
    Formula.satisfies η (tg_even0_m a) ↔ Tg_even_d a (η.bound 0) (η.bound 1) (η.bound 2) := by
  simp only [tg_even0_m,Tg_even_d,rb_exists_sat_l,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,rd_entry0_sat_l hE,rt_tuple_sat_l hE,Definitional.Term.eval_weaken,
    Term.eval_bound,Fin.addCases_left,Fin.addCases_right]
  rfl

theorem It_frames_d.even_branch_l (hZF : M.Models ZF) {n} {idx : Fin 14 → Fin (n+1)}
    {ω c D f : M.Domain} {U : Fin 6 → M.Domain} (h : It_frames_d hZF idx ω c D f)
    (tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3))
    (columns : ∀ b x, M.mem x (U b) ↔ Tg_run_value_d (idx ⟨8+b.val,by omega⟩) f x)
    (heads : ∀ i s (v : Fin (n+1) → M.Domain), Rd_entry_d i s f → Rt_tuple_d v s →
      M.SuccessorOf (v (idx 6)) (v (idx 7))) :
    ∃ B, It_branch_d ω (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d (idx 7) f (U 0) x := by
  let φ : UnarySchema 2 := {
    body := (tg_even0_m (idx 7)).bind (fun i => [.bound 1,.bound 2,.newest].get i)
    freeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _).mpr (tg_even0_closed_l _) }
  let η : Env M 2 := ⟨fun i => [f,U 0].get i,fun _ => f⟩
  have sat x : φ.denote η x ↔ Tg_even_d (idx 7) f (U 0) x := by
    rw [UnarySchema.denote,Formula.satisfies_bind,tg_even0_sat_l hZF.1]; rfl
  obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ η ω
  have bound {x} (hx : Tg_even_d (idx 7) f (U 0) x) : M.mem x ω := by
    obtain ⟨v,_,_,_,_,edge⟩ := hx
    exact (tree.diagram.order.bound x (v (idx 7)) edge).1
  have iff x : M.mem x B ↔ Tg_even_d (idx 7) f (U 0) x := (bs x).trans
    ((and_congr_right fun _ => sat x).trans ⟨And.right,fun hx => ⟨bound hx,hx⟩⟩)
  have keep {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {x y} (xy : Rd_entry_d x y (v (idx 8))) : Rd_entry_d x y (U 0) := by
    obtain ⟨p,pair,hp⟩ := xy
    exact ⟨p,pair,(columns 0 p).mpr ⟨v,i,s,hs,code,hp⟩⟩
  refine ⟨B,⟨fun x hx => bound ((iff x).mp hx),?_,?_,?_⟩,iff⟩
  · intro x y hx hy
    obtain ⟨v,i,s,hs,ps,xv⟩ := (iff x).mp hx
    obtain ⟨w,j,t,ht,pt,yw⟩ := (iff y).mp hy
    obtain ⟨k,r,z,hr,pr,vz,wz⟩ := h.merge i j s t v w hs ht ps pt
    have vh := keep hr pr (vz.2.2.2 (v (idx 7))
      ((h.read_l hZF v hs ps).tree.diagram.order.refl _ (heads i s v hs ps).predecessor_mem))
    have wh := keep hr pr (wz.2.2.2 (w (idx 7))
      ((h.read_l hZF w ht pt).tree.diagram.order.refl _ (heads j t w ht pt).predecessor_mem))
    exact tree.diagram.order.chain x y (z (idx 7))
      (tree.diagram.order.trans x _ _ xv vh) (tree.diagram.order.trans y _ _ yw wh)
  · intro x y xy hy
    obtain ⟨v,i,s,hs,ps,yv⟩ := (iff y).mp hy
    exact (iff x).mpr ⟨v,i,s,hs,ps,tree.diagram.order.trans x y (v (idx 7)) xy yv⟩
  · intro i hi
    obtain ⟨s,_,hs⟩ := h.function.2.1 i hi
    obtain ⟨v,code,frame⟩ := h.rows i s hs
    have succ := heads i s v hs code
    have hv := tree.omega.transitive (ZF.modelsKP hZF) _ frame.finite _ succ.predecessor_mem
    exact ⟨v (idx 7),(iff _).mpr ⟨v,i,s,hs,code,tree.diagram.order.refl _ hv⟩,
      ((succ i).mp frame.span).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members i _ eq))⟩

end YesMetaZFC.SetTheory.LargeCardinal
