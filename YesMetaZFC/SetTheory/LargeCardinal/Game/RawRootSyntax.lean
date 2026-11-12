import YesMetaZFC.SetTheory.LargeCardinal.Game.RawSavedBase
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.RootSquare
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 原根切片及保存时下界的完整对象语言

相对根关系、完整前驱方程和实际根图全部编码。保存下界量化所有实际
五十四项读取码；共尾证书只记录严格切片需要的不可数共尾度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_root_square_m {d} (D p q g : Term d) : Formula 1 d := set[d] ⟪
  ∀ a ∈ ⌜D⌝ₛ, ∀ x, ⌜rd_entry0_m⌝ₚ(a,x,⌜p⌝ₛ) → ∀ y,
    (⌜rd_entry0_m⌝ₚ(x,y,⌜g⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(a,y,⌜q⌝ₛ))⟫
derive_free_closed tg_root_square_m

theorem tg_root_square_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D p q g : Term d) :
    Formula.satisfies ρ (tg_root_square_m D p q g) ↔
      Tg_root_square_d (D.eval ρ) (p.eval ρ) (q.eval ρ) (g.eval ρ) := by
  simp only [tg_root_square_m,Tg_root_square_d,Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

-- X₀,R₀,γ₀,D₀,C₀,X,R,C,q,γ,V,t。
def tg_root_slice_m {d} (p : Fin 12 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜rd_entry0_m⌝ₚ(⌜p 4⌝ₛ,⌜p 7⌝ₛ,⌜p 8⌝ₛ) ∧
    ⌜rr_rank_m⌝ₚ(⌜p 5⌝ₛ,⌜p 6⌝ₛ,⌜p 9⌝ₛ,⌜p 10⌝ₛ)⟫)
    (.conj (rr_truth_m (𝒞 := kpair_convention_l) (Formula.isLimitOrdinal .newest)
      (p 5) (p 6) (fun _ : Fin 1 => p 9))
    (set[d] ⟪⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜p 11⌝ₛ,⌜p 3⌝ₛ,⌜p 5⌝ₛ) ∧
      (∀ y, ⌜rd_entry0_m⌝ₚ(y,⌜p 10⌝ₛ,⌜p 6⌝ₛ) ↔
        (∃ x ∈ ⌜p 3⌝ₛ, ⌜rd_entry0_m⌝ₚ(x,y,⌜p 11⌝ₛ))) ∧
      (∀ x y, ⌜rd_entry0_m⌝ₚ(x,y,⌜p 11⌝ₛ) → ∀ z,
        (⌜rd_entry0_m⌝ₚ(z,y,⌜p 6⌝ₛ) ↔ ∃ a,
          ⌜rd_entry0_m⌝ₚ(a,x,⌜p 1⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(a,z,⌜p 11⌝ₛ))) ∧
      ⌜er_rep_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 5⌝ₛ,⌜p 6⌝ₛ,⌜p 11⌝ₛ,⌜p 2⌝ₛ,⌜p 9⌝ₛ) ∧
      (∀ x y, ⌜rd_entry0_m⌝ₚ(x,y,⌜p 11⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,y,⌜p 8⌝ₛ))⟫))

@[simp] theorem tg_root_slice_closed_l {d} (p : Fin 12 → Term d)
    (hp : ∀ i, (p i).freeSupport = []) : (tg_root_slice_m p).FreeClosed := by
  simp -implicitDefEqProofs [tg_root_slice_m,Definitional.Formula.FreeClosed,hp]
  exact rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ (hp 5) (hp 6) (fun _ => hp 9)

theorem tg_root_slice_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (p : Fin 12 → Term d) :
    Formula.satisfies ρ (tg_root_slice_m p) ↔
      Tg_root_slice_d I ((p 0).eval ρ) ((p 1).eval ρ) ((p 2).eval ρ) ((p 3).eval ρ)
        ((p 4).eval ρ) ((p 5).eval ρ) ((p 6).eval ρ) ((p 7).eval ρ) ((p 8).eval ρ)
        ((p 9).eval ρ) ((p 10).eval ρ) ((p 11).eval ρ) := by
  simp only [tg_root_slice_m,Formula.satisfies_conj_iff,rd_entry0_sat_l hE,rr_rank_sat_l I,
    rr_truth_sat_l I _ (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs),
    Formula.satisfies_isInjectionFromTo_iff I hE,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,Formula.satisfies_imp_iff,
    er_rep_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨⟨a,b⟩,c,d,e,f,g,h⟩ => ⟨a,b,c,d,e,f,g,h⟩,
    fun h => ⟨⟨h.context,h.rank⟩,h.limit,h.injection,h.image,h.predecessors,h.endpoint,h.root⟩⟩

private def tg_raw_saved_bound_m {d} (X R w U q γ : Term d) : Formula 1 d :=
  let e : Term d → Term (54+d) := fun t => t.rename (Fin.natAdd 54)
  rb_forall_m (n := 54) (.imp
    (tg_saved_code_m (e X) (e R) (e w) (e U) (e q) (fun i => .bound (i.castAdd d)))
    (set[54+d] ⟪∀ x, ⌜rd_entry0_m⌝ₚ(x,⌜e γ⌝ₛ,⌜e R⌝ₛ) →
      ⌜rd_entry0_m⌝ₚ(x,⌜(.bound ((15 : Fin 54).castAdd d) : Term (54+d))⌝ₛ,⌜e R⌝ₛ)⟫))

@[simp] private theorem tg_raw_saved_bound_closed_l {d} (X R w U q γ : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hw : w.freeSupport = [])
    (hU : U.freeSupport = []) (hq : q.freeSupport = []) (hγ : γ.freeSupport = []) :
    (tg_raw_saved_bound_m X R w U q γ).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_saved_bound_m,Definitional.Formula.FreeClosed,hX,hR,hw,hU,hq,hγ]

private theorem tg_raw_saved_bound_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (X R w U q γ : Term d) : Formula.satisfies ρ (tg_raw_saved_bound_m X R w U q γ) ↔
      ∀ v : Fin 54 → M.Domain, Tg_saved_code_d (X.eval ρ) (R.eval ρ) (w.eval ρ) (U.eval ρ) (q.eval ρ) v →
        ∀ x, Rd_entry_d x (γ.eval ρ) (R.eval ρ) → Rd_entry_d x (v 15) (R.eval ρ) := by
  simp only [tg_raw_saved_bound_m,rb_forall_sat_l,Formula.satisfies_imp_iff,tg_saved_code_sat_l,
    Formula.satisfies_forall_iff,rd_entry0_sat_l hE,Definitional.Term.eval_weaken,rb_old_eval_l,
    Term.eval_bound,Fin.addCases_left]
  rfl

-- X₀,R₀,γ₀,D₀,C₀,X,R,w,C,U,q,p。
def tg_raw_saved_base_m {d} (p : Fin 12 → Term d) : Formula 1 d :=
  let e : Term d → Term (3+d) := fun t => t.rename (Fin.natAdd 3)
  rb_exists_m (n := 3) (.conj (tg_root_slice_m (fun i =>
    [e (p 0),e (p 1),e (p 2),e (p 3),e (p 4),e (p 5),e (p 6),e (p 8),e (p 11),
      .bound ((0 : Fin 3).castAdd d),.bound ((1 : Fin 3).castAdd d),.bound ((2 : Fin 3).castAdd d)].get i))
    (.conj (rd_entry0_m (e (p 7)) (.bound ((1 : Fin 3).castAdd d)) (e (p 6)))
      (tg_raw_saved_bound_m (e (p 5)) (e (p 6)) (e (p 7)) (e (p 9)) (e (p 10))
        (.bound ((0 : Fin 3).castAdd d)))))

@[simp] theorem tg_raw_saved_base_closed_l {d} (p : Fin 12 → Term d)
    (hp : ∀ i, (p i).freeSupport = []) : (tg_raw_saved_base_m p).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_saved_base_m,Definitional.Formula.FreeClosed,hp,Fin.forall_fin_succ]

theorem tg_raw_saved_base_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (p : Fin 12 → Term d) :
    Formula.satisfies ρ (tg_raw_saved_base_m p) ↔
      Tg_raw_saved_base_d I ((p 0).eval ρ) ((p 1).eval ρ) ((p 2).eval ρ) ((p 3).eval ρ)
        ((p 4).eval ρ) ((p 5).eval ρ) ((p 6).eval ρ) ((p 7).eval ρ) ((p 8).eval ρ)
        ((p 9).eval ρ) ((p 10).eval ρ) ((p 11).eval ρ) := by
  simp only [tg_raw_saved_base_m,rb_exists_sat_l,Formula.satisfies_conj_iff,tg_root_slice_sat_l I hE,
    rd_entry0_sat_l hE,tg_raw_saved_bound_sat_l hE,rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get]
  constructor
  · rintro ⟨v,slice,omega,bound⟩
    exact ⟨v 0,v 1,v 2,slice,omega,bound⟩
  · rintro ⟨γ,V,t,slice,omega,bound⟩
    exact ⟨(fun i => [γ,V,t].get i),slice,omega,bound⟩

def tg_raw_cofinal_m {d} (w X R L : Term d) : Formula 1 d := .existsE
  (.conj (rd_entry0_m w.weaken .newest R.weaken)
    (rr_truth_m (𝒞 := kpair_convention_l) (Formula.isCofinality kpair_convention_l (.bound 0) (.bound 1))
      X.weaken R.weaken (Fin.cases .newest (fun _ : Fin 1 => L.weaken))))

@[simp] theorem tg_raw_cofinal_closed_l {d} (w X R L : Term d)
    (hw : w.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hL : L.freeSupport = []) :
    (tg_raw_cofinal_m w X R L).FreeClosed := by
  simp only [tg_raw_cofinal_m,Definitional.Formula.FreeClosed]
  refine ⟨by simp -implicitDefEqProofs [hw,hR] ,rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ ?_ ?_ ?_⟩
  · simpa using hX
  · simpa using hR
  · exact Fin.cases rfl (fun _ => by simpa using hL)

theorem tg_raw_cofinal_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (w X R L : Term d) :
    Formula.satisfies ρ (tg_raw_cofinal_m w X R L) ↔
      Tg_raw_cofinal_d I (w.eval ρ) (X.eval ρ) (R.eval ρ) (L.eval ρ) := by
  simp only [tg_raw_cofinal_m,Tg_raw_cofinal_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,rr_truth_sat_l I _
      (Formula.isCofinality kpair_convention_l (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs),
    Definitional.Term.eval_weaken]
  apply exists_congr
  intro ν
  apply and_congr_right
  intro _
  let v : Fin 2 → Term (d+1) := Fin.cases .newest (fun _ : Fin 1 => L.weaken)
  have values : (fun i : Fin 2 => (v i).eval (ρ.push ν)) = Fin.cases ν (fun _ : Fin 1 => L.eval ρ) :=
    funext (Fin.cases rfl (fun _ => Definitional.Term.eval_weaken ρ ν L))
  exact values ▸ Iff.rfl

end YesMetaZFC.SetTheory.LargeCardinal
