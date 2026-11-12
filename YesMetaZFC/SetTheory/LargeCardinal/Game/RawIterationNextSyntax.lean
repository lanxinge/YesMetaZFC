import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveEdge
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationNext
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationSyntax

/-! # 十一项原档案的父边与重置方程编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def tg_raw_archive_step_body_m {d} (s t : Fin 11 → Term d) (j : Term d)
    (v w : Fin 54 → Term d) (a : Fin 5 → Term d) : Formula 1 d :=
  .conj (tg_saved_code_m (s 2) (s 3) (s 4) (s 8) (s 9) v)
    (.conj (tg_saved_code_m (t 2) (t 3) (t 4) (t 8) (t 9) w)
      (.conj (rb_conj_m (fun i : Fin 5 => Formula.orderedPairMem kpair_convention_l
        (v ([19,22,40,41,42].get i)) (a i) j)) (tg_restart_link_m (t 2) (t 3) a w)))

def tg_raw_archive_step_m {d} (s t : Fin 11 → Term d) (j : Term d) : Formula 1 d :=
  let e : Term d → Term (54+d) := fun x => x.rename (Fin.natAdd 54)
  let f : Term (54+d) → Term (54+(54+d)) := fun x => x.rename (Fin.natAdd 54)
  let g : Term (54+(54+d)) → Term (5+(54+(54+d))) := fun x => x.rename (Fin.natAdd 5)
  rb_exists_m (n := 54) (rb_exists_m (n := 54) (rb_exists_m (n := 5) (tg_raw_archive_step_body_m
    (fun i => g (f (e (s i)))) (fun i => g (f (e (t i)))) (g (f (e j)))
    (fun i => g (f (.bound (i.castAdd d)))) (fun i => g (.bound (i.castAdd (54+d))))
    (fun i => .bound (i.castAdd (54+(54+d)))))))

@[simp] theorem tg_raw_archive_step_closed_l {d} (s t : Fin 11 → Term d) (j : Term d)
    (hs : ∀ i, (s i).freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) (hj : j.freeSupport = []) :
    (tg_raw_archive_step_m s t j).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_step_m,tg_raw_archive_step_body_m,Definitional.Formula.FreeClosed,hs,ht,hj]

theorem tg_raw_archive_step_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (s t : Fin 11 → Term d) (j : Term d) :
    Formula.satisfies ρ (tg_raw_archive_step_m s t j) ↔
      Tg_raw_archive_step_d I (Tg_raw_archive_row_d.from_values_d (fun i => (s i).eval ρ))
        (Tg_raw_archive_row_d.from_values_d (fun i => (t i).eval ρ)) (j.eval ρ) := by
  simp only [tg_raw_archive_step_m,tg_raw_archive_step_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    tg_saved_code_sat_l,rb_conj_sat_l,Formula.satisfies_orderedPairMem_iff I,tg_restart_link_sat_l I hE,
    Definitional.Term.eval_rename,Env.reindex,Function.comp_def,Term.eval_bound,Fin.addCases_left,Fin.addCases_right]
  unfold Tg_raw_archive_step_d
  constructor
  · rintro ⟨v,w,a,cv,cw,points,link⟩
    exact ⟨v,w,cv,cw,a,points,link⟩
  · rintro ⟨v,w,cv,cw,a,points,link⟩
    exact ⟨v,w,a,cv,cw,points,link⟩

def tg_raw_archive_reset_m {d} (t : Fin 11 → Term d) (S j : Term d) : Formula 1 d :=
  let e : Term d → Term (54+d) := fun x => x.rename (Fin.natAdd 54)
  let v : Fin 54 → Term (54+d) := fun i => .bound (i.castAdd d)
  rb_exists_m (.conj (tg_saved_code_m (e (t 2)) (e (t 3)) (e (t 4)) (e (t 8)) (e (t 9)) v)
    (set[54+d] ⟪⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜e S⌝ₛ,⌜v 19⌝ₛ,⌜e j⌝ₛ) ∧
      ⌜v 22⌝ₛ = ⌜v 17⌝ₛ ∧ ⌜v 40⌝ₛ = ⌜v 17⌝ₛ ∧ ⌜v 41⌝ₛ = ⌜v 17⌝ₛ ∧ ⌜v 42⌝ₛ = ⌜v 17⌝ₛ⟫))

@[simp] theorem tg_raw_archive_reset_closed_l {d} (t : Fin 11 → Term d) (S j : Term d)
    (ht : ∀ i, (t i).freeSupport = []) (hS : S.freeSupport = []) (hj : j.freeSupport = []) :
    (tg_raw_archive_reset_m t S j).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_reset_m,Definitional.Formula.FreeClosed,ht,hS,hj]

theorem tg_raw_archive_reset_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (t : Fin 11 → Term d) (S j : Term d) :
    Formula.satisfies ρ (tg_raw_archive_reset_m t S j) ↔
      Tg_raw_archive_reset_d I (Tg_raw_archive_row_d.from_values_d (fun i => (t i).eval ρ)) (S.eval ρ) (j.eval ρ) := by
  simp only [tg_raw_archive_reset_m,Tg_raw_archive_reset_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    tg_saved_code_sat_l,Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_extensionalEq_iff_eq hE,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 十一项实际选行及原父边的一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def tg_raw_parent_old_m {d} (v : Fin 20 → Term d) (a : Fin 46 → Term d)
    (k j : Term d) (t : Fin 11 → Term d) : Formula 1 d :=
  let e : Term d → Term (13+d) := fun x => x.rename (Fin.natAdd 13)
  let s : Fin 11 → Term (13+d) := fun i => .bound ((i.castAdd 2).castAdd d)
  let l : Term (13+d) := .bound ((11 : Fin 13).castAdd d)
  let r : Term (13+d) := .bound ((12 : Fin 13).castAdd d)
  rb_exists_m (n := 13) (.conj (.mem l (e (v 18)))
    (.conj (Formula.orderedPairMem kpair_convention_l l (e (a 22)) (e (v 3)))
      (.conj (Formula.orderedPairMem kpair_convention_l l r (e (v 13)))
        (.conj (rt_tuple_m s r) (.conj (Formula.extensionalEq (s 0) (e k))
          (tg_raw_archive_step_m s (fun i => e (t i)) (e j)))))))

private theorem tg_raw_parent_old_closed_l {d} (v : Fin 20 → Term d) (a : Fin 46 → Term d)
    (k j : Term d) (t : Fin 11 → Term d)
    (hv : ∀ i, (v i).freeSupport = []) (ha : ∀ i, (a i).freeSupport = [])
    (hk : k.freeSupport = []) (hj : j.freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) :
    (tg_raw_parent_old_m v a k j t).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_parent_old_m,Definitional.Formula.FreeClosed,hv,ha,hk,hj,ht]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

private theorem tg_raw_parent_old_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (v : Fin 20 → Term d) (a : Fin 46 → Term d) (k j : Term d) (t : Fin 11 → Term d) :
    Formula.satisfies ρ (tg_raw_parent_old_m v a k j t) ↔
      ∃ l r, ∃ s : Tg_raw_archive_row_d M.Domain,
        M.mem l ((v 18).eval ρ) ∧ M.PairMember I l ((a 22).eval ρ) ((v 3).eval ρ) ∧
        M.PairMember I l r ((v 13).eval ρ) ∧ Rt_tuple_d s.values_d r ∧ s.i = k.eval ρ ∧
        Tg_raw_archive_step_d I s (Tg_raw_archive_row_d.from_values_d (fun i => (t i).eval ρ)) (j.eval ρ) := by
  simp only [tg_raw_parent_old_m,rb_exists_sat_l,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I,rt_tuple_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,
    tg_raw_archive_step_sat_l I hE,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,hl,point,entry,code,eq,step⟩
    refine ⟨u 11,u 12,Tg_raw_archive_row_d.from_values_d (fun i => u (i.castAdd 2)),hl,point,entry,?_,eq,step⟩
    simpa only [Tg_raw_archive_row_d.values_from_l] using code
  · rintro ⟨l,r,s,hl,point,entry,code,eq,step⟩
    let u : Fin 13 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) s.values_d (fun i => [l,r].get i)
    have coords : (fun i : Fin 11 => u (i.castAdd 2)) = s.values_d :=
      funext (fun i => Fin.addCases_left (m := 11) (n := 2) (motive := fun _ => M.Domain)
        (left := s.values_d) (right := fun i : Fin 2 => [l,r].get i) i)
    refine ⟨u,hl,point,entry,?_,eq,?_⟩
    · exact Eq.mpr (congrArg (fun v => Rt_tuple_d v r) coords) code
    · have row : Tg_raw_archive_row_d.from_values_d (fun i => u (i.castAdd 2)) = s :=
        (congrArg Tg_raw_archive_row_d.from_values_d coords).trans (Tg_raw_archive_row_d.from_values_l s)
      exact row.symm ▸ step

def tg_raw_iteration_parent_m {d} (v : Fin 20 → Term d) (a : Fin 46 → Term d)
    (k G : Term d) (t : Fin 11 → Term d) : Formula 1 d := .existsE
  (.conj (it_map_m G.weaken k.weaken (v 6).weaken .newest)
    (.disj (.conj (Formula.extensionalEq (a 23).weaken (a 1).weaken)
      (.conj (Formula.extensionalEq k.weaken (v 7).weaken)
        (tg_raw_archive_reset_m (fun i => (t i).weaken) (a 7).weaken .newest)))
      (.conj (.neg (Formula.extensionalEq (a 23).weaken (a 1).weaken))
        (tg_raw_parent_old_m (fun i => (v i).weaken) (fun i => (a i).weaken) k.weaken .newest (fun i => (t i).weaken)))))

@[simp] theorem tg_raw_iteration_parent_closed_l {d} (v : Fin 20 → Term d) (a : Fin 46 → Term d)
    (k G : Term d) (t : Fin 11 → Term d)
    (hv : ∀ i, (v i).freeSupport = []) (ha : ∀ i, (a i).freeSupport = [])
    (hk : k.freeSupport = []) (hG : G.freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) :
    (tg_raw_iteration_parent_m v a k G t).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_parent_m,Definitional.Formula.FreeClosed,hv,ha,hk,hG,ht,
    tg_raw_parent_old_closed_l]

theorem tg_raw_iteration_parent_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d)
    (v : Fin 20 → Term d) (a : Fin 46 → Term d) (k G : Term d) (t : Fin 11 → Term d) :
    Formula.satisfies ρ (tg_raw_iteration_parent_m v a k G t) ↔
      Tg_raw_iteration_parent_d hZF (fun i => (v i).eval ρ) (fun i => (a i).eval ρ) (k.eval ρ) (G.eval ρ)
        (Tg_raw_archive_row_d.from_values_d (fun i => (t i).eval ρ)) := by
  simp only [tg_raw_iteration_parent_m,Tg_raw_iteration_parent_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,it_map_sat_l hZF.1,Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_neg_iff,
    tg_raw_archive_reset_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    tg_raw_parent_old_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生两步延伸、原字母追加与十一项档案的一阶编码

十三项尾部存在块只保存新行、行码和真实原字母；控制历史的包含按
目标原关系逐点解释，与语义后继使用完全相同的两条树边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private def tg_raw_iteration_tail_m {d} (ω A x : Term d) (v w : Fin 20 → Term d)
    (a : Fin 46 → Term d) (k G : Term d) : Formula 1 d :=
  let e : Term d → Term (13+d) := fun t => t.rename (Fin.natAdd 13)
  let s : Fin 11 → Term (13+d) := fun i => .bound ((i.castAdd 2).castAdd d)
  let r : Term (13+d) := .bound ((11 : Fin 13).castAdd d)
  let y : Term (13+d) := .bound ((12 : Fin 13).castAdd d)
  rb_exists_m (n := 13) (.conj (.mem y (e A))
    (.conj (fseq_end_m (𝒞 := kpair_convention_l) (e ω) (e (w 19)) (e (v 19)) y)
      (.conj (.imp (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (e ω) (e (v 18))) (Formula.extensionalEq y (e x)))
        (.conj (Formula.extensionalEq (s 0) (e (v 6))) (.conj (rt_tuple_m s r)
          (.conj (tg_raw_iteration_parent_m (fun i => e (v i)) (fun i => e (a i)) (e k) (e G) s)
            (set[13+d] ⟪∀ l t, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(l,t,⌜e (w 13)⌝ₛ) ↔
              ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(l,t,⌜e (v 13)⌝ₛ) ∨ (l = ⌜e (v 18)⌝ₛ ∧ t = ⌜r⌝ₛ)⟫)))))))

private theorem tg_raw_iteration_tail_closed_l {d} (ω A x : Term d) (v w : Fin 20 → Term d)
    (a : Fin 46 → Term d) (k G : Term d) (hω : ω.freeSupport = [])
    (hA : A.freeSupport = []) (hx : x.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (ha : ∀ i, (a i).freeSupport = []) (hk : k.freeSupport = []) (hG : G.freeSupport = []) :
    (tg_raw_iteration_tail_m ω A x v w a k G).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_tail_m,Definitional.Formula.FreeClosed,hω,hA,hx,hv,hw,ha,hk,hG]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

private theorem tg_raw_iteration_tail_sat_l {d} (ρ : Env M d) (ω A x : Term d) (v w : Fin 20 → Term d)
    (a : Fin 46 → Term d) (k G : Term d) : Formula.satisfies ρ (tg_raw_iteration_tail_m ω A x v w a k G) ↔
      ∃ y, M.mem y (A.eval ρ) ∧ Fseq_end_d I (ω.eval ρ) ((w 19).eval ρ) ((v 19).eval ρ) y ∧
        (Descriptive.Gm_even_d I (ω.eval ρ) ((v 18).eval ρ) → y = x.eval ρ) ∧
        ∃ s : Tg_raw_archive_row_d M.Domain, ∃ r, s.i = (v 6).eval ρ ∧ Rt_tuple_d s.values_d r ∧
          Tg_raw_iteration_parent_d hZF (fun i => (v i).eval ρ) (fun i => (a i).eval ρ) (k.eval ρ) (G.eval ρ) s ∧
          (∀ l t, M.PairMember I l t ((w 13).eval ρ) ↔ M.PairMember I l t ((v 13).eval ρ) ∨ l = (v 18).eval ρ ∧ t = r) := by
  simp only [tg_raw_iteration_tail_m,rb_exists_sat_l,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    fseq_end_sat_l I hZF.1,Formula.satisfies_imp_iff,Descriptive.gm_even_sat_l I hZF.1,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,rt_tuple_sat_l hZF.1,tg_raw_iteration_parent_sat_l hZF,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_disj_iff,Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,member,ends,even,index,code,parent,entries⟩
    refine ⟨u 12,member,ends,even,Tg_raw_archive_row_d.from_values_d (fun i => u (i.castAdd 2)),u 11,index,?_,parent,entries⟩
    simpa only [Tg_raw_archive_row_d.values_from_l] using code
  · rintro ⟨y,member,ends,even,s,r,index,code,parent,entries⟩
    let u : Fin 13 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) s.values_d (fun i => [r,y].get i)
    have coords : (fun i : Fin 11 => u (i.castAdd 2)) = s.values_d :=
      funext (fun i => Fin.addCases_left (m := 11) (n := 2) (motive := fun _ => M.Domain)
        (left := s.values_d) (right := fun i : Fin 2 => [r,y].get i) i)
    have row := (congrArg Tg_raw_archive_row_d.from_values_d coords).trans (Tg_raw_archive_row_d.from_values_l s)
    exact ⟨u,member,ends,even,index,Eq.mpr (congrArg (fun v => Rt_tuple_d v r) coords) code,row.symm ▸ parent,entries⟩

private def tg_raw_iteration_next_body_m {d} (ω c A x : Term d) (v w : Fin 20 → Term d)
    (a b : Fin 46 → Term d) (e : Fin 6 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜it_tree_m⌝ₚ(⌜ω⌝ₛ,⌜c⌝ₛ,⌜w 7⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ) ∧
    ⌜it_extension_m⌝ₚ(⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜e 0⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ,⌜w 7⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ) ∧
    ⌜it_extension_m⌝ₚ(⌜w 7⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜e 1⌝ₛ,⌜e 2⌝ₛ,⌜e 3⌝ₛ,⌜e 4⌝ₛ,⌜w 6⌝ₛ,⌜w 8⌝ₛ,⌜w 9⌝ₛ,⌜w 10⌝ₛ,⌜w 11⌝ₛ) ∧
    ⌜it_map_m⌝ₚ(⌜w 10⌝ₛ,⌜v 7⌝ₛ,⌜w 7⌝ₛ,⌜e 5⌝ₛ)⟫)
  (.conj (rb_conj_m (fun i : Fin 19 => Formula.orderedPairMem kpair_convention_l
    (a (i.castAdd 27)) (b (i.castAdd 27)) (e 5)))
  (.conj (set[d] ⟪(∃ t, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜a 20⌝ₛ,t,⌜e 5⌝ₛ) ∧
      ¬ (t = ⌜b 20⌝ₛ) ∧ (∀ y, ⌜rd_entry0_m⌝ₚ(y,t,⌜w 1⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y,⌜b 20⌝ₛ,⌜w 1⌝ₛ))) ∧
    ⌜KP.succ0_m⌝ₚ(⌜w 18⌝ₛ,⌜v 18⌝ₛ)⟫)
    (tg_raw_iteration_tail_m ω A x v w a (e 0) (e 3))))

def tg_raw_iteration_next_m {d} (ω c A x : Term d) (v w : Fin 20 → Term d)
    (a b : Fin 46 → Term d) : Formula 1 d :=
  let r : Term d → Term (6+d) := fun t => t.rename (Fin.natAdd 6)
  rb_exists_m (n := 6) (tg_raw_iteration_next_body_m (r ω) (r c) (r A) (r x)
    (fun i => r (v i)) (fun i => r (w i)) (fun i => r (a i)) (fun i => r (b i)) (fun i => .bound (i.castAdd d)))

@[simp] theorem tg_raw_iteration_next_closed_l {d} (ω c A x : Term d) (v w : Fin 20 → Term d)
    (a b : Fin 46 → Term d) (hω : ω.freeSupport = []) (hc : c.freeSupport = [])
    (hA : A.freeSupport = []) (hx : x.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (ha : ∀ i, (a i).freeSupport = []) (hb : ∀ i, (b i).freeSupport = []) :
    (tg_raw_iteration_next_m ω c A x v w a b).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_next_m,tg_raw_iteration_next_body_m,Definitional.Formula.FreeClosed,
    hω,hc,hA,hx,hv,hw,ha,hb,tg_raw_iteration_tail_closed_l]

theorem tg_raw_iteration_next_sat_l {d} (ρ : Env M d) (ω c A x : Term d)
    (v w : Fin 20 → Term d) (a b : Fin 46 → Term d) :
    Formula.satisfies ρ (tg_raw_iteration_next_m ω c A x v w a b) ↔
      Tg_raw_iteration_next_d hZF (ω.eval ρ) (c.eval ρ) (A.eval ρ) (x.eval ρ)
        (fun i => (v i).eval ρ) (fun i => (w i).eval ρ) (fun i => (a i).eval ρ) (fun i => (b i).eval ρ) := by
  simp only [tg_raw_iteration_next_m,tg_raw_iteration_next_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    it_tree_sat_l hZF,it_extension_sat_l hZF.1,it_map_sat_l hZF.1,rb_conj_sat_l,
    Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    rd_entry0_sat_l hZF.1,KP.succ0_sat_l hZF.1,tg_raw_iteration_tail_sat_l hZF,
    Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨e,⟨tree,first,second,edge⟩,points,⟨strict,succ⟩,tail⟩
    exact ⟨e 0,e 1,e 2,e 3,e 4,e 5,tree,first,second,edge,points,strict,succ,tail⟩
  · rintro ⟨k,T,Q,G,E,j,tree,first,second,edge,points,strict,succ,tail⟩
    exact ⟨(fun i => [k,T,Q,G,E,j].get i),⟨tree,first,second,edge⟩,points,⟨strict,succ⟩,tail⟩

end YesMetaZFC.SetTheory.LargeCardinal
