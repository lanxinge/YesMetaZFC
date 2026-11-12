import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchive
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax

/-! # 十一项原档案及所选共同列的一阶编码

固定有限坐标只描述行的形状，行、原记录和共同图仍由对象量词完整遍历。
源根切片、不可数共尾度和同图根方块逐项保留，不引入工作复制坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_raw_archive_row_d.from_values_d {α : Type u} (v : Fin 11 → α) : Tg_raw_archive_row_d α :=
  ⟨v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10⟩

@[simp] theorem Tg_raw_archive_row_d.values_from_l {α : Type u} (v : Fin 11 → α) :
    (Tg_raw_archive_row_d.from_values_d v).values_d = v :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun i => Fin.elim0 i))))))))))))

theorem Tg_raw_archive_row_d.from_values_l {α : Type u} (s : Tg_raw_archive_row_d α) :
    Tg_raw_archive_row_d.from_values_d s.values_d = s := by cases s; rfl

-- X,R,w,U,q,g,N,S,w',C,c,e,a,b,z,m,h；v 是原五十四项码。
private def tg_raw_saved_view_body_m {d} (r : Fin 17 → Term d) (v : Fin 54 → Term d) : Formula 1 d :=
  .conj (tg_saved_code_m (r 0) (r 1) (r 2) (r 3) (r 4) v) (set[d] ⟪∃ n t κ u,
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 15⌝ₛ,n,⌜r 14⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 41⌝ₛ,t,⌜r 5⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 15⌝ₛ,κ,⌜r 5⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 11⌝ₛ,u,⌜r 5⌝ₛ) ∧
    ⌜tg_trace_m⌝ₚ(⌜r 6⌝ₛ,⌜r 7⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 10⌝ₛ,⌜r 11⌝ₛ,⌜r 12⌝ₛ,n,⌜r 16⌝ₛ,t,κ,u) ∧
    (∃ s, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 40⌝ₛ,s,⌜r 5⌝ₛ) ∧
      ⌜tg_play_m⌝ₚ(⌜r 6⌝ₛ,⌜r 7⌝ₛ,⌜r 9⌝ₛ,⌜r 10⌝ₛ,⌜r 13⌝ₛ,⌜r 16⌝ₛ,s))⟫)

def tg_raw_saved_view0_m : Formula 1 17 := rb_exists_m (tg_raw_saved_view_body_m
  (fun i => .bound (Fin.natAdd 54 i)) (fun i => .bound (i.castAdd 17)))

theorem tg_raw_saved_view0_closed_l : tg_raw_saved_view0_m.FreeClosed := by
  rw [tg_raw_saved_view0_m,rb_exists_closed_l]
  simp -implicitDefEqProofs [tg_raw_saved_view_body_m,Definitional.Formula.FreeClosed]

theorem tg_raw_saved_view0_sat_l (I : kpair_convention_l.Interpretation M) (ρ : Env M 17) :
    Formula.satisfies ρ tg_raw_saved_view0_m ↔
      Tg_raw_saved_view_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5)
        (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12)
        (ρ.bound 13) (ρ.bound 14) (ρ.bound 15) (ρ.bound 16) := by
  rw [tg_raw_saved_view0_m,rb_exists_sat_l]
  unfold Tg_raw_saved_view_d
  apply exists_congr
  intro v
  simp only [tg_raw_saved_view_body_m,Formula.satisfies_conj_iff,tg_saved_code_sat_l,
    Formula.satisfies_exists_iff,Formula.satisfies_orderedPairMem_iff I,tg_trace_sat_l I,tg_play_sat_l I,
    Definitional.Term.eval_weaken,Term.eval_bound,Fin.addCases_left,Fin.addCases_right]
  rfl

def tg_raw_saved_view_m {d} (r : Fin 17 → Term d) : Formula 1 d := tg_raw_saved_view0_m.bind r

@[simp] theorem tg_raw_saved_view_closed_l {d} (r : Fin 17 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_raw_saved_view_m r).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ hr _).mpr tg_raw_saved_view0_closed_l

theorem tg_raw_saved_view_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d)
    (r : Fin 17 → Term d) : Formula.satisfies ρ (tg_raw_saved_view_m r) ↔
      Tg_raw_saved_view_d I ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ) ((r 4).eval ρ)
        ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ) ((r 10).eval ρ)
        ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ) ((r 15).eval ρ) ((r 16).eval ρ) := by
  rw [tg_raw_saved_view_m,Formula.satisfies_bind,tg_raw_saved_view0_sat_l I]
  rfl

-- Ω,S₀,X₀,R₀,γ₀,D₀,C₀,p,N,S,χ,w,C,c,e,a,b,z,h,m,r；v 是十一项原行。
private def tg_raw_archive_entry_body_m {d} (r : Fin 21 → Term d) (v : Fin 11 → Term d) : Formula 1 d :=
  .conj (rt_tuple_m v (r 20)) (set[d] ⟪
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ) ∧
    ⌜tg_saved_m⌝ₚ(⌜v 4⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ) ∧
    (∃ z, ⌜rr_layer_m⌝ₚ(⌜r 0⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,z)) ∧
    ⌜tg_saved_name_m⌝ₚ(⌜r 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ) ∧
    ⌜fun X₀ R₀ γ₀ D₀ C₀ X R w C U q p => tg_raw_saved_base_m
      (fun i => [X₀,R₀,γ₀,D₀,C₀,X,R,w,C,U,q,p].get i)⌝ₚ(⌜r 2⌝ₛ,⌜r 3⌝ₛ,⌜r 4⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,
      ⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ) ∧
    ⌜tg_raw_cofinal_m⌝ₚ(⌜v 4⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 7⌝ₛ) ∧
    (∃ l V Γ g, ⌜ic_common_m⌝ₚ(⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜v 7⌝ₛ,l,⌜v 8⌝ₛ,V,Γ,g) ∧
      (⌜rd_entry0_m⌝ₚ(l,⌜r 10⌝ₛ,⌜r 9⌝ₛ) ∨ l = ⌜r 10⌝ₛ) ∧
      ⌜tg_root_square_m⌝ₚ(⌜r 5⌝ₛ,⌜v 10⌝ₛ,⌜r 7⌝ₛ,g) ∧
      ⌜fun X R w U q g N S w' C c e a b z m h => tg_raw_saved_view_m
        (fun i => [X,R,w,U,q,g,N,S,w',C,c,e,a,b,z,m,h].get i)⌝ₚ
        (⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,g,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 11⌝ₛ,
          ⌜r 12⌝ₛ,⌜r 13⌝ₛ,⌜r 14⌝ₛ,⌜r 15⌝ₛ,⌜r 16⌝ₛ,⌜r 17⌝ₛ,⌜r 19⌝ₛ,⌜r 18⌝ₛ))⟫)

def tg_raw_archive_entry_m {d} (r : Fin 21 → Term d) : Formula 1 d := rb_exists_m
  (tg_raw_archive_entry_body_m (fun i => (r i).rename (Fin.natAdd 11)) (fun i => .bound (i.castAdd d)))

@[simp] theorem tg_raw_archive_entry_closed_l {d} (r : Fin 21 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_raw_archive_entry_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_entry_m,tg_raw_archive_entry_body_m,
    Definitional.Formula.FreeClosed,hr,Fin.forall_fin_succ]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr 20)

theorem tg_raw_archive_entry_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r : Fin 21 → Term d) :
    Formula.satisfies ρ (tg_raw_archive_entry_m r) ↔
      Tg_raw_archive_entry_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ) ((r 17).eval ρ) ((r 18).eval ρ) ((r 19).eval ρ) ((r 20).eval ρ) := by
  simp only [tg_raw_archive_entry_m,tg_raw_archive_entry_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hKP.1,smdl_sat_l (kp_pair_l hKP),tg_saved_sat_l (kp_pair_l hKP) hKP.1,
    Formula.satisfies_exists_iff,rr_layer_sat_l (kp_pair_l hKP) hKP.1,tg_saved_name_sat_l (kp_pair_l hKP),
    tg_raw_saved_base_sat_l (kp_pair_l hKP) hKP.1,tg_raw_cofinal_sat_l (kp_pair_l hKP) hKP.1,ic_common_sat_l hKP,
    Formula.satisfies_disj_iff,rd_entry0_sat_l hKP.1,Formula.satisfies_extensionalEq_iff_eq hKP.1,
    tg_root_square_sat_l hKP.1,tg_raw_saved_view_sat_l (kp_pair_l hKP),Definitional.Term.eval_weaken,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get,Definitional.Term.eval_newest]
  constructor
  · rintro ⟨v,h⟩
    refine ⟨Tg_raw_archive_row_d.from_values_d v,?_,h.2⟩
    simpa only [Tg_raw_archive_row_d.values_from_l] using h.1
  · rintro ⟨s,h⟩
    exact ⟨s.values_d,h⟩

-- D,o,n,Q,G,Λ；一次量化十一项行、外部轮号及行码。
private def tg_raw_archive_link_body_m {d} (r : Fin 6 → Term d) (v : Fin 13 → Term d) : Formula 1 d :=
  .imp (Formula.orderedPairMem kpair_convention_l (v 11) (v 12) (r 0))
    (.imp (rt_tuple_m (fun i => v (i.castAdd 2)) (v 12)) (set[d] ⟪
      ⌜v 0⌝ₛ ∈ ⌜r 2⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜r 3⌝ₛ) ∧
      ⌜it_map_m⌝ₚ(⌜r 4⌝ₛ,⌜r 1⌝ₛ,⌜v 0⌝ₛ,⌜v 10⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 0⌝ₛ,⌜v 7⌝ₛ,⌜r 5⌝ₛ)⟫))

def tg_raw_archive_links_m {d} (r : Fin 6 → Term d) : Formula 1 d := rb_forall_m
  (tg_raw_archive_link_body_m (fun i => (r i).rename (Fin.natAdd 13)) (fun i => .bound (i.castAdd d)))

@[simp] theorem tg_raw_archive_links_closed_l {d} (r : Fin 6 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_raw_archive_links_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_links_m,tg_raw_archive_link_body_m,Definitional.Formula.FreeClosed,hr]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_raw_archive_links_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (r : Fin 6 → Term d) : Formula.satisfies ρ (tg_raw_archive_links_m r) ↔
      Tg_raw_archive_links_d I ⟨(r 1).eval ρ,(r 2).eval ρ,(r 3).eval ρ,(r 4).eval ρ,(r 5).eval ρ⟩ ((r 0).eval ρ) := by
  simp only [tg_raw_archive_links_m,tg_raw_archive_link_body_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,rt_tuple_sat_l hE,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,rd_entry0_sat_l hE,it_map_sat_l hE,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · intro h m t s entry code
    let v : Fin 13 → M.Domain := Fin.addCases (m := 11) (n := 2) s.values_d (Fin.cases m (fun _ => t))
    exact h v entry code
  · intro h v entry code
    have code' : Rt_tuple_d (Tg_raw_archive_row_d.from_values_d (fun i => v (i.castAdd 2))).values_d (v 12) := by
      rw [Tg_raw_archive_row_d.values_from_l]
      exact code
    exact h (v 11) (v 12) (Tg_raw_archive_row_d.from_values_d (fun i => v (i.castAdd 2))) entry code'

-- Ω,S₀,X₀,R₀,γ₀,D₀,C₀,p,D,N,S,χ,w,C,c,e,a,b,z,h。
def tg_raw_archive_views_m {d} (r : Fin 20 → Term d) : Formula 1 d :=
  let t : Fin 20 → Term (2+d) := fun i => (r i).rename (Fin.natAdd 2)
  let a : Fin 2 → Term (2+d) := fun i => .bound (i.castAdd d)
  rb_forall_m (.imp (Formula.orderedPairMem kpair_convention_l (a 0) (a 1) (t 8))
    (tg_raw_archive_entry_m (fun i => [t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7,t 9,t 10,t 11,t 12,t 13,
      t 14,t 15,t 16,t 17,t 18,t 19,a 0,a 1].get i)))

@[simp] theorem tg_raw_archive_views_closed_l {d} (r : Fin 20 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_raw_archive_views_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_views_m,Definitional.Formula.FreeClosed,hr,Fin.forall_fin_succ]

theorem tg_raw_archive_views_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r : Fin 20 → Term d) :
    Formula.satisfies ρ (tg_raw_archive_views_m r) ↔
      Tg_raw_archive_views_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ) ((r 17).eval ρ) ((r 18).eval ρ) ((r 19).eval ρ) := by
  simp only [tg_raw_archive_views_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),tg_raw_archive_entry_sat_l hKP,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get]
  exact ⟨fun h m r => h (fun i => [m,r].get i),fun h v => h (v 0) (v 1)⟩

end YesMetaZFC.SetTheory.LargeCardinal
