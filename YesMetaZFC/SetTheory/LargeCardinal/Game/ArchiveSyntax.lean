import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedView
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.Archive

/-! # 共同有限状态中基底、历史界与原局的完整编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_basis_m {d} (γ B C₀ w X R C p : Term d) : Formula 1 d := set[d] ⟪
  ⌜rd_entry0_m⌝ₚ(⌜C₀⌝ₛ,⌜C⌝ₛ,⌜p⌝ₛ) ∧ (∃ a V z t,
  ⌜rr_layer_m⌝ₚ(⌜γ⌝ₛ,⌜X⌝ₛ,⌜R⌝ₛ,a,z) ∧ ⌜rr_layer_m⌝ₚ(⌜B⌝ₛ,⌜X⌝ₛ,⌜R⌝ₛ,V,t) ∧
  ⌜rr_rank_m⌝ₚ(⌜X⌝ₛ,⌜R⌝ₛ,a,V) ∧
  ⌜fun X R a => rr_truth_m (𝒞 := kpair_convention_l) (Formula.isLimitOrdinal (.newest : Term 1)) X R (fun _ => a)⌝ₚ(⌜X⌝ₛ,⌜R⌝ₛ,a) ∧
  ⌜rd_entry0_m⌝ₚ(⌜w⌝ₛ,V,⌜R⌝ₛ) ∧ (∀ x y, ⌜rd_entry0_m⌝ₚ(x,y,t) → ⌜rd_entry0_m⌝ₚ(x,y,⌜p⌝ₛ)))⟫
@[simp] theorem tg_basis_closed_l {d} (γ B C₀ w X R C p : Term d)
    (hγ : γ.freeSupport = []) (hB : B.freeSupport = []) (hC₀ : C₀.freeSupport = [])
    (hw : w.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hC : C.freeSupport = []) (hp : p.freeSupport = []) : (tg_basis_m γ B C₀ w X R C p).FreeClosed := by
  simp -implicitDefEqProofs [tg_basis_m,Definitional.Formula.FreeClosed,hγ,hB,hC₀,hw,hX,hR,hC,hp]
  exact rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _
    (by simpa using hX) (by simpa using hR) (fun _ => rfl)

theorem tg_basis_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (γ B C₀ w X R C p : Term d) :
    Formula.satisfies ρ (tg_basis_m γ B C₀ w X R C p) ↔
      Tg_basis_d I (γ.eval ρ) (B.eval ρ) (C₀.eval ρ) (w.eval ρ) (X.eval ρ) (R.eval ρ) (C.eval ρ) (p.eval ρ) := by
  simp only [tg_basis_m,Tg_basis_d,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,
    rd_entry0_sat_l hE,rr_layer_sat_l I hE,rr_rank_sat_l I,
    rr_truth_sat_l I _ (Formula.isLimitOrdinal (.newest : Term 1)) (by simp -implicitDefEqProofs),
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原存档、事件与实数前缀视图的完整编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- X,R,w,U,q,γ,g,N,S,w',C,c,e,a,b,z,m,h。
private def tg_saved_view_body_m {d} (r : Fin 18 → Term d) (v : Fin 54 → Term d) : Formula 1 d :=
  .conj (tg_saved_code_m (r 0) (r 1) (r 2) (r 3) (r 4) v)
    (.conj (it_lower_m (r 5) (r 0) (r 1) (v 15)) (set[d] ⟪∃ n t κ u,
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 16⌝ₛ,n,⌜r 15⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 41⌝ₛ,t,⌜r 6⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 15⌝ₛ,κ,⌜r 6⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 11⌝ₛ,u,⌜r 6⌝ₛ) ∧
      ⌜tg_trace_m⌝ₚ(⌜r 7⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ,⌜r 10⌝ₛ,⌜r 11⌝ₛ,⌜r 12⌝ₛ,⌜r 13⌝ₛ,n,⌜r 17⌝ₛ,t,κ,u) ∧
      (∃ s, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 40⌝ₛ,s,⌜r 6⌝ₛ) ∧
        ⌜tg_play_m⌝ₚ(⌜r 7⌝ₛ,⌜r 8⌝ₛ,⌜r 10⌝ₛ,⌜r 11⌝ₛ,⌜r 14⌝ₛ,⌜r 17⌝ₛ,s))⟫))

def tg_saved_view0_m : Formula 1 18 := rb_exists_m (tg_saved_view_body_m
  (fun i => .bound (Fin.natAdd 54 i)) (fun i => .bound (i.castAdd 18)))

theorem tg_saved_view0_closed_l : tg_saved_view0_m.FreeClosed := by
  rw [tg_saved_view0_m,rb_exists_closed_l]
  simp -implicitDefEqProofs [tg_saved_view_body_m,Definitional.Formula.FreeClosed]

theorem tg_saved_view0_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 18) : Formula.satisfies ρ tg_saved_view0_m ↔
      Tg_saved_view_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5)
        (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12)
        (ρ.bound 13) (ρ.bound 14) (ρ.bound 15) (ρ.bound 16) (ρ.bound 17) := by
  rw [tg_saved_view0_m,rb_exists_sat_l]
  unfold Tg_saved_view_d
  apply exists_congr
  intro v
  simp only [tg_saved_view_body_m,Formula.satisfies_conj_iff,tg_saved_code_sat_l,
    it_lower_sat_l I hE,Formula.satisfies_exists_iff,Formula.satisfies_orderedPairMem_iff I,
    tg_trace_sat_l I,tg_play_sat_l I,Definitional.Term.eval_weaken,Term.eval_bound,
    Fin.addCases_left,Fin.addCases_right]
  rfl

def tg_saved_view_m {d} (r : Fin 18 → Term d) : Formula 1 d := tg_saved_view0_m.bind r

@[simp] theorem tg_saved_view_closed_l {d} (r : Fin 18 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_saved_view_m r).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ hr _).mpr tg_saved_view0_closed_l

theorem tg_saved_view_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (r : Fin 18 → Term d) : Formula.satisfies ρ (tg_saved_view_m r) ↔
      Tg_saved_view_d I ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ) ((r 4).eval ρ)
        ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ) ((r 10).eval ρ)
        ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ) ((r 15).eval ρ)
        ((r 16).eval ρ) ((r 17).eval ρ) := by
  rw [tg_saved_view_m,Formula.satisfies_bind,tg_saved_view0_sat_l I hE]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部原档案行、根名字与当前视图的一阶编码

十三项行码保留原模型和原存档；跨模型关系均经实际图解释。
坐标块量词同时覆盖模型内部的全部行，不能用外部标准有限枚举代替。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_archive_row_d.from_values_d {α : Type u} (v : Fin 13 → α) : Tg_archive_row_d α :=
  ⟨v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12⟩

@[simp] theorem Tg_archive_row_d.values_from_l {α : Type u} (v : Fin 13 → α) :
    (Tg_archive_row_d.from_values_d v).values_d = v :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))))))))

theorem Tg_archive_row_d.from_values_l {α : Type u} (s : Tg_archive_row_d α) :
    Tg_archive_row_d.from_values_d s.values_d = s := by cases s; rfl

-- Ω,γ,Bγ,C₀,N,S,B,σ,w,C,c,e,a,b,z,h,m,r；v 是十三项原行。
private def tg_archive_entry_body_m {d} (r : Fin 18 → Term d) (v : Fin 13 → Term d) : Formula 1 d :=
  .conj (rt_tuple_m v (r 17)) (set[d] ⟪
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ) ∧
    ⌜tg_saved_m⌝ₚ(⌜v 4⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ) ∧
    (∃ z, ⌜rr_layer_m⌝ₚ(⌜r 0⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,z)) ∧
    ⌜tg_basis_m⌝ₚ(⌜r 1⌝ₛ,⌜r 2⌝ₛ,⌜r 3⌝ₛ,⌜v 4⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 6⌝ₛ,⌜v 10⌝ₛ) ∧
    (∃ l φ V Γ g,
      ⌜ic_agree_m⌝ₚ(⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 11⌝ₛ,⌜v 12⌝ₛ,⌜r 4⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 7⌝ₛ,⌜v 7⌝ₛ,l,φ,⌜v 8⌝ₛ,V,Γ,g) ∧
      ⌜fun X R w U q γ g N S w' C c e a b z m h => tg_saved_view_m
        (fun i => [X,R,w,U,q,γ,g,N,S,w',C,c,e,a,b,z,m,h].get i)⌝ₚ
        (⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜r 1⌝ₛ,g,⌜r 4⌝ₛ,⌜r 5⌝ₛ,⌜r 8⌝ₛ,
          ⌜r 9⌝ₛ,⌜r 10⌝ₛ,⌜r 11⌝ₛ,⌜r 12⌝ₛ,⌜r 13⌝ₛ,⌜r 14⌝ₛ,⌜r 16⌝ₛ,⌜r 15⌝ₛ))⟫)

def tg_archive_entry_m {d} (r : Fin 18 → Term d) : Formula 1 d := rb_exists_m
  (tg_archive_entry_body_m (fun i => (r i).rename (Fin.natAdd 13)) (fun i => .bound (i.castAdd d)))

@[simp] theorem tg_archive_entry_closed_l {d} (r : Fin 18 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_archive_entry_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_entry_m,tg_archive_entry_body_m,Definitional.Formula.FreeClosed,
    hr,Fin.forall_fin_succ]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr 17)

theorem tg_archive_entry_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r : Fin 18 → Term d) :
    Formula.satisfies ρ (tg_archive_entry_m r) ↔
      Tg_archive_entry_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ) ((r 17).eval ρ) := by
  simp only [tg_archive_entry_m,tg_archive_entry_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hKP.1,smdl_sat_l (kp_pair_l hKP),tg_saved_sat_l (kp_pair_l hKP) hKP.1,
    Formula.satisfies_exists_iff,rr_layer_sat_l (kp_pair_l hKP) hKP.1,tg_basis_sat_l (kp_pair_l hKP) hKP.1,
    ic_agree_sat_l hKP,tg_saved_view_sat_l (kp_pair_l hKP) hKP.1,Definitional.Term.eval_weaken,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get,Definitional.Term.eval_newest]
  constructor
  · rintro ⟨v,h⟩
    refine ⟨Tg_archive_row_d.from_values_d v,?_,h.2⟩
    simpa only [Tg_archive_row_d.values_from_l] using h.1
  · rintro ⟨s,h⟩
    exact ⟨s.values_d,h⟩

-- H,o,n,Q,G,L,复制历史；一次量化十三项原行及外部轮号、行码。
private def tg_archive_link_body_m {d} (r : Fin 7 → Term d) (v : Fin 15 → Term d) : Formula 1 d :=
  .imp (Formula.orderedPairMem kpair_convention_l (v 13) (v 14) (r 0))
    (.imp (rt_tuple_m (fun i => v (i.castAdd 2)) (v 14)) (set[d] ⟪
      ⌜v 0⌝ₛ ∈ ⌜r 2⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜r 3⌝ₛ) ∧
      ⌜it_map_m⌝ₚ(⌜r 4⌝ₛ,⌜r 1⌝ₛ,⌜v 0⌝ₛ,⌜v 10⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 0⌝ₛ,⌜v 7⌝ₛ,⌜r 5⌝ₛ) ∧
      (∃ z Z α, ⌜ic_at_m⌝ₚ(⌜r 6⌝ₛ,⌜v 0⌝ₛ,⌜v 2⌝ₛ,⌜v 11⌝ₛ,⌜v 12⌝ₛ,z,Z,α))⟫))

def tg_archive_links_m {d} (r : Fin 7 → Term d) : Formula 1 d := rb_forall_m
  (tg_archive_link_body_m (fun i => (r i).rename (Fin.natAdd 15)) (fun i => .bound (i.castAdd d)))

@[simp] theorem tg_archive_links_closed_l {d} (r : Fin 7 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_archive_links_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_links_m,tg_archive_link_body_m,Definitional.Formula.FreeClosed,hr]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_archive_links_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (r : Fin 7 → Term d) : Formula.satisfies ρ (tg_archive_links_m r) ↔
      Tg_archive_links_d I ⟨(r 1).eval ρ,(r 2).eval ρ,(r 3).eval ρ,(r 4).eval ρ,(r 5).eval ρ,(r 6).eval ρ⟩ ((r 0).eval ρ) := by
  simp only [tg_archive_links_m,tg_archive_link_body_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,rt_tuple_sat_l hE,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,rd_entry0_sat_l hE,it_map_sat_l hE,Formula.satisfies_exists_iff,
    ic_at_sat_l hE,Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · intro h m t s entry code
    let v : Fin 15 → M.Domain := Fin.addCases (m := 13) (n := 2) s.values_d (Fin.cases m (fun _ => t))
    have result := h v
    exact result entry code
  · intro h v entry code
    have code' : Rt_tuple_d (Tg_archive_row_d.from_values_d (fun i => v (i.castAdd 2))).values_d (v 14) := by
      rw [Tg_archive_row_d.values_from_l]
      exact code
    exact h (v 13) (v 14) (Tg_archive_row_d.from_values_d (fun i => v (i.castAdd 2))) entry code'

def tg_archive_names_m {d} (S H : Term d) : Formula 1 d :=
  let v : Fin 15 → Term (15+d) := fun i => .bound (i.castAdd d)
  rb_forall_m (.imp (Formula.orderedPairMem kpair_convention_l (v 13) (v 14) (H.rename (Fin.natAdd 15)))
    (.imp (rt_tuple_m (fun i => v (i.castAdd 2)) (v 14))
      (tg_saved_name_m (S.rename (Fin.natAdd 15)) (v 2) (v 3) (v 4) (v 8) (v 9) (v 10))))

@[simp] theorem tg_archive_names_closed_l {d} (S H : Term d)
    (hS : S.freeSupport = []) (hH : H.freeSupport = []) : (tg_archive_names_m S H).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_names_m,Definitional.Formula.FreeClosed,hS,hH]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_archive_names_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (S H : Term d) : Formula.satisfies ρ (tg_archive_names_m S H) ↔
      Tg_archive_names_d I (S.eval ρ) (H.eval ρ) := by
  simp only [tg_archive_names_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,rt_tuple_sat_l hE,tg_saved_name_sat_l I,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · intro h m t s entry code
    let v : Fin 15 → M.Domain := Fin.addCases (m := 13) (n := 2) s.values_d (Fin.cases m (fun _ => t))
    have result := h v
    exact result entry code
  · intro h v entry code
    have code' : Rt_tuple_d (Tg_archive_row_d.from_values_d (fun i => v (i.castAdd 2))).values_d (v 14) := by
      rw [Tg_archive_row_d.values_from_l]
      exact code
    exact h (v 13) (v 14) (Tg_archive_row_d.from_values_d (fun i => v (i.castAdd 2))) entry code'

end YesMetaZFC.SetTheory.LargeCardinal
