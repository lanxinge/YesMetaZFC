import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.Descriptive.Game
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 交替博弈输入的确定递归及有限前缀因果性

只读取偶数位置的对手输入；奇数位置及尚未给出的输入统一使用固定字母。
响应表预先固定后，递归仅用 ZF。相同有限输入必定产生相同的当前状态。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Gi_input_d (ω a f n x : M.Domain) : Prop := (Gm_even_d I ω n ∧ Rd_entry_d n x f) ∨
  (¬ (Gm_even_d I ω n ∧ ∃ y, Rd_entry_d n y f)) ∧ x = a
def gi_input_m {d} (ω a f n x : Term d) : Formula 1 d := set[d] ⟪
  (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ,⌜x⌝ₛ,⌜f⌝ₛ)) ∨
  (¬ (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) ∧ (∃ y, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ,y,⌜f⌝ₛ)))) ∧ ⌜x⌝ₛ = ⌜a⌝ₛ⟫
derive_free_closed gi_input_m
theorem gi_input_sat_l {d} (ρ : Env M d) (ω a f n x : Term d) :
    Formula.satisfies ρ (gi_input_m ω a f n x) ↔ Gi_input_d hZF (ω.eval ρ) (a.eval ρ) (f.eval ρ) (n.eval ρ) (x.eval ρ) := by
  simp only [gi_input_m,Gi_input_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,gm_even_sat_l I hZF.1,
    rd_entry0_sat_l hZF.1,Formula.satisfies_neg_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]; rfl
theorem Gi_input_d.unique_l {ω a f n x y : M.Domain} (fn : M.IsSetFunction I f)
    (h : Gi_input_d hZF ω a f n x) (g : Gi_input_d hZF ω a f n y) : x = y := by
  rcases h with ⟨he,hx⟩ | ⟨hn,rfl⟩ <;> rcases g with ⟨he',hy⟩ | ⟨hn',rfl⟩
  · exact fn.2 n x y hx hy
  · exact (hn' ⟨he,x,hx⟩).elim
  · exact (hn ⟨he',y,hy⟩).elim
  · rfl

def Gi_d (ω X K r a f H : M.Domain) : Prop := Fn0_d ω X H ∧
  (∀ o, (∀ z, ¬ M.mem z o) → Rd_entry_d o r H) ∧
  ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
    ∃ x p, Gi_input_d hZF ω a f i x ∧ (I).Codes p s x ∧ Rd_entry_d p t K
def gi_m {d} (ω X K r a f H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜H⌝ₛ) ∧ (∀ o, (∀ z, ¬ z ∈ o) → ⌜rd_entry0_m⌝ₚ(o,⌜r⌝ₛ,⌜H⌝ₛ)) ∧
  (∀ i j s t, ⌜KP.succ0_m⌝ₚ(j,i) → ⌜rd_entry0_m⌝ₚ(i,s,⌜H⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j,t,⌜H⌝ₛ) →
    ∃ x p, ⌜gi_input_m⌝ₚ(⌜ω⌝ₛ,⌜a⌝ₛ,⌜f⌝ₛ,i,x) ∧ ⌜kpair_m⌝ₚ(p,s,x) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ))⟫
derive_free_closed gi_m
theorem gi_sat_l {d} (ρ : Env M d) (ω X K r a f H : Term d) : Formula.satisfies ρ (gi_m ω X K r a f H) ↔
    Gi_d hZF (ω.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (f.eval ρ) (H.eval ρ) := by
  simp only [gi_m,Gi_d,Formula.satisfies_conj_iff,fn0_sat_l hZF.1,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,rd_entry0_sat_l hZF.1,
    KP.succ0_sat_l hZF.1,Formula.satisfies_exists_iff,gi_input_sat_l hZF,kpair_sat_l M hZF.1,
    Definitional.Term.eval_weaken]; rfl

theorem gi_exists_l {ω A X D K r a f : M.Domain} (hw : M.IsOmega ω)
    (prod : M.IsCartesianProduct I D X A) (fn : Fn0_d D X K) (hr : M.mem r X) (ha : M.mem a A)
    (ff : M.IsSetFunction I f) (range : ∀ i x, Rd_entry_d i x f → M.mem x A) : ∃ H, Gi_d hZF ω X K r a f H := by
  classical
  have input i : ∃ x, M.mem x A ∧ Gi_input_d hZF ω a f i x := by
    by_cases h : Gm_even_d I ω i ∧ ∃ x, Rd_entry_d i x f
    · obtain ⟨he,x,hx⟩ := h; exact ⟨x,range i x hx,Or.inl ⟨he,hx⟩⟩
    · exact ⟨a,ha,Or.inr ⟨h,rfl⟩⟩
  obtain ⟨E,ep⟩ := ZF.exists_cartesianProduct hZF I ω X
  let ρ : Env M 4 := ⟨fun i => [ω,a,f,K].get i,fun _ => ω⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪∃ i s x p,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ,i,s) ∧
    ⌜gi_input_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ,i,x) ∧
    ⌜kpair_m⌝ₚ(p,s,x) ∧ ⌜rd_entry0_m⌝ₚ(p,⌜(.newest : Term 6)⌝ₛ,⌜(.bound 5 : Term 6)⌝ₛ)⟫ }
  have sat q t : φ.denote ρ q t ↔ ∃ i s x p, (I).Codes q i s ∧ Gi_input_d hZF ω a f i x ∧
      (I).Codes p s x ∧ Rd_entry_d p t K := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,gi_input_sat_l hZF,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have fk := fn0_function_l (ZF.modelsKP hZF) fn
  obtain ⟨L,lf,ls⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := E) (target := X) (by
    intro q hq
    obtain ⟨i,_,s,hs,pair⟩ := (ep q).mp hq
    obtain ⟨x,hx,inp⟩ := input i
    obtain ⟨p,px⟩ := (I).total s x
    obtain ⟨t,_,ht⟩ := fn.2.1 p ((prod p).mpr ⟨s,hs,x,hx,px⟩)
    exact ⟨t,(sat q t).mpr ⟨i,s,x,p,pair,inp,px,ht⟩⟩) (by
    intro q _ t u ht hu
    obtain ⟨i,s,x,p,pair,inp,px,ht⟩ := (sat q t).mp ht
    obtain ⟨j,z,y,q',pair',inp',py,hu⟩ := (sat q u).mp hu
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    have xy := inp.unique_l hZF ff inp'
    have pq := (I).unique px (xy.symm ▸ py)
    exact fk.1.2 p t u ht (pq.symm ▸ hu)) (by
    intro q t _ ht
    obtain ⟨_,_,_,p,_,_,_,ht⟩ := (sat q t).mp ht
    exact (fn.bound_l ht).2)
  obtain ⟨H,hf,hz,steps⟩ := ZF.indexed_iteration_l I hZF hw ep lf hr
  refine ⟨H,fn0_of_function_l (ZF.modelsKP hZF) hf,hz,fun i j s t succ hs ht => ?_⟩
  obtain ⟨q,pair,qt⟩ := steps i j s t succ hs ht
  obtain ⟨i',s',x,p,pair',inp,px,pt⟩ := (sat q t).mp ((ls q t).mp qt).2
  obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
  exact ⟨x,p,inp,px,pt⟩

theorem Gi_d.agree_l {ω X K r a f g H G n : M.Domain} (hw : M.IsOmega ω)
    (kf : M.IsSetFunction I K) (ff : M.IsSetFunction I f) (h : Gi_d hZF ω X K r a f H)
    (g' : Gi_d hZF ω X K r a g G) (hn : M.mem n ω)
    (same : ∀ i, M.mem i n → ∀ x, Gi_input_d hZF ω a f i x ↔ Gi_input_d hZF ω a g i x) :
    ∀ s t, Rd_entry_d n s H → Rd_entry_d n t G → s = t := by
  let ρ : Env M 3 := ⟨fun i => [n,H,G].get i,fun _ => n⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪(⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ ∨
    ⌜(.newest : Term 4)⌝ₛ = ⌜(.bound 1 : Term 4)⌝ₛ) → ∀ s t,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,s,⌜(.bound 2 : Term 4)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,t,⌜(.bound 3 : Term 4)⌝ₛ) → s = t⟫ }
  have sat i : φ.denote ρ i ↔ (M.mem i n ∨ i = n) → ∀ s t, Rd_entry_d i s H → Rd_entry_d i t G → s = t := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_forall_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have hf := fn0_function_l (ZF.modelsKP hZF) h.1
  have gf := fn0_function_l (ZF.modelsKP hZF) g'.1
  have all : ∀ i, M.mem i ω → (M.mem i n ∨ i = n) → ∀ s t, Rd_entry_d i s H → Rd_entry_d i t G → s = t := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun i => (bs i).trans (and_congr_right fun _ => sat i)⟩
    · intro o ho _ s t hs ht
      exact (hf.1.2 o s r hs (h.2.1 o ho)).trans (gf.1.2 o r t (g'.2.1 o ho) ht)
    · intro i hi ih j succ bound s t hs ht
      have hin : M.mem i n := bound.elim (fun hj => (hw.members_areOrdinals hZF n hn).transitive j hj i succ.predecessor_mem)
        (fun eq => eq ▸ succ.predecessor_mem)
      obtain ⟨u,_,hu⟩ := h.1.2.1 i hi
      obtain ⟨v,_,hv⟩ := g'.1.2.1 i hi
      obtain ⟨x,p,inp,pair,pt⟩ := h.2.2 i j u s succ hu hs
      obtain ⟨y,q,inp',pair',qt⟩ := g'.2.2 i j v t succ hv ht
      have xy := inp.unique_l hZF ff ((same i hin y).mpr inp')
      have pq := (I).unique pair ((ih (Or.inl hin) u v hu hv).symm ▸ xy.symm ▸ pair')
      exact kf.2 p s t pt (pq.symm ▸ qt)
  exact all n hn (Or.inr rfl)

theorem Gi_d.prefix_l {ω X K r a f g H G n : M.Domain} (hw : M.IsOmega ω)
    (kf : M.IsSetFunction I K) (ff : M.IsSetFunction I f) (h : Gi_d hZF ω X K r a f H)
    (g' : Gi_d hZF ω X K r a g G) (hn : M.mem n ω) (cut : M.IsRestrictionOf I g f n) :
    ∀ s t, Rd_entry_d n s H → Rd_entry_d n t G → s = t := by
  apply h.agree_l hZF hw kf ff g' hn
  intro i hi x
  have ent y : Rd_entry_d i y g ↔ Rd_entry_d i y f := (cut.2 i y).trans (and_iff_right hi)
  simp only [Gi_input_d,ent]

end YesMetaZFC.SetTheory.Descriptive
