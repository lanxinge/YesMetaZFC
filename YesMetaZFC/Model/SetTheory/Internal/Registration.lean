import YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative
import YesMetaZFC.SetTheory.Card.Cofinality.Comparison

/-! # 条件与固定参数列的同枚举登记

位置表逐项指出原列在目标枚举中的位置；只在输入及输出位置同时可见时检查。
同一谓词用于条件列和固定参数列，因此任意总枝同时保证条件和必要常量进入壳。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Rg_d (e f v : M.Domain) : Prop := ∀ i k x, Rd_entry_d i k v → Rd_entry_d i x f → Rd_entry_d k x e

def Rg_at_d (n e f v : M.Domain) : Prop := ∀ i k x, M.mem i n → M.mem k n →
  Rd_entry_d i k v → Rd_entry_d i x f → Rd_entry_d k x e

def rg_at_m {a} (n e f v : Term a) : Formula 1 a := set[a] ⟪∀ i k x,
  i ∈ ⌜n⌝ₛ → k ∈ ⌜n⌝ₛ → ⌜rd_entry0_m⌝ₚ(i,k,⌜v⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i,x,⌜f⌝ₛ) → ⌜rd_entry0_m⌝ₚ(k,x,⌜e⌝ₛ)⟫
derive_free_closed rg_at_m

theorem rg_at_sat_l (hE : Extensional M) {a} (ρ : Env M a) (n e f v : Term a) :
    Formula.satisfies ρ (rg_at_m n e f v) ↔ Rg_at_d (n.eval ρ) (e.eval ρ) (f.eval ρ) (v.eval ρ) := by
  simp only [rg_at_m,Rg_at_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem Rg_at_d.prefix_l {X n m e f v e' f' v' : M.Domain} (h : Rg_at_d m e f v)
    (fe : Fn0_d m X e) (fn : Fn0_d n X e')
    (ee : M.MemberSubset e' e) (ff : M.MemberSubset f' f) (vv : M.MemberSubset v' v) : Rg_at_d n e' f' v' := by
  have move {F G a b : M.Domain} (sub : M.MemberSubset F G) (ab : Rd_entry_d a b F) : Rd_entry_d a b G :=
    ab.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  have sub : M.MemberSubset n m := fun i hi => (fn.2.1 i hi).elim fun _ h => (fe.bound_l (move ee h.2)).1
  intro i k x hi hk ik ix
  have kx := h i k x (sub i hi) (sub k hk) (move vv ik) (move ff ix)
  obtain ⟨y,hy,ky⟩ := fn.2.1 k hk
  have eq := fe.2.2 k (sub k hk) y hy x (fe.bound_l kx).2 (move ee ky) kx
  exact eq ▸ ky

theorem Rg_d.range_l {ω X N e f v : M.Domain} (h : Rg_d e f v)
    (fe : Fn0_d ω N e) (ff : Fn0_d ω X f) (fv : Fn0_d ω ω v) : Fn0_d ω N f := by
  apply ff.retarget_l
  intro i x ix
  obtain ⟨k,_,ik⟩ := fv.2.1 i (ff.bound_l ix).1
  exact (fe.bound_l (h i k x ik ix)).2

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rg_lift_l {ω N e f : M.Domain} (hw : M.IsOmega ω) (fe : Fn0_d ω N e)
    (onto : M.IsSetSurjectiveOnto I e ω N) (ff : Fn0_d ω N f) : ∃ v, Fn0_d ω ω v ∧ Rg_d e f v := by
  obtain ⟨ι,inj,section'⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I
    (hw.isOrdinal (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF) fe) onto
  have fi := fn0_of_function_l (ZF.modelsKP hZF) inj.1
  obtain ⟨v,comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ff fi
  exact ⟨v,comp.1,fun i k x ik ix => section' x k ((comp.value_l ff fi ix).mp ik)⟩

/-- 源列只按可见坐标读取；固定参数列无需截成节点内部的新对象。 -/
theorem rg_branch_l {ω e f v : M.Domain} (hw : M.IsOmega ω) (fv : Fn0_d ω ω v)
    (prefixes : ∀ n, M.mem n ω → ∃ a b, Rg_at_d n a f b ∧ M.IsRestrictionOf I a e n ∧ M.IsRestrictionOf I b v n) :
    Rg_d e f v := by
  intro i k x ik ix
  obtain ⟨n,hn,hin,hkn⟩ := at_upper_l hZF hw (fv.bound_l ik).1 (fv.bound_l ik).2
  obtain ⟨a,b,check,cut,table⟩ := prefixes n hn
  exact ((cut.2 k x).mp (check i k x hin hkn ((table.2 i k).mpr ⟨hin,ik⟩) ix)).2

end YesMetaZFC.SetTheory.Internal
