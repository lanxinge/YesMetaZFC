import YesMetaZFC.Model.SetTheory.Internal.SkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.Membership

/-! # 集合隶属结构中的统一司寇伦见证公式

载体 X 的结构码在公式内部唯一确定，因此可用同一条原公式表达全部内部公式码
的存在见证；不对整个背景宇宙假设可定义真值。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smem_d (c X R : M.Domain) : Prop := Smdl_d I c X R ∧
  ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y

def smem_m {n} (c X R : Term n) : Formula 1 n := .conj (smdl_m (𝒞 := 𝒞) c X R)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
    (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken) (.mem (.bound 1) .newest))))))
derive_free_closed smem_m

theorem smem_sat_l {n} (ρ : Env M n) (c X R : Term n) :
    Formula.satisfies ρ (smem_m (𝒞 := 𝒞) c X R) ↔ Smem_d I (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [smem_m, Smem_d, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem smem_unique_l (hE : Extensional M) {c X R d S} (h : Smem_d I c X R) (k : Smem_d I d X S) :
    c = d ∧ R = S := by
  have he := h.1.2.2.1.eq_of_pairMember_iff hE k.1.2.2.1 (fun x y => (h.2 x y).trans (k.2 x y).symm)
  subst S
  exact ⟨I.unique h.1.1 k.1.1, rfl⟩

def Ssk_mem_d (ω X u a i s x : M.Domain) : Prop := ∃ c R,
  Smem_d I c X R ∧ M.mem x X ∧ Ssk_wit_d I ω c X u a i s x

def ssk_mem_m {d} (ω X u a i s x : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (smem_m (𝒞 := 𝒞) (.bound 1) X.weaken.weaken .newest)
    (.conj (.mem x.weaken.weaken X.weaken.weaken)
      (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) X.weaken.weaken u.weaken.weaken
        a.weaken.weaken i.weaken.weaken s.weaken.weaken x.weaken.weaken))))
derive_free_closed ssk_mem_m

theorem ssk_mem_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X u a i s x : Term d) :
    Formula.satisfies ρ (ssk_mem_m (𝒞 := 𝒞) ω X u a i s x) ↔
      Ssk_mem_d I (ω.eval ρ) (X.eval ρ) (u.eval ρ) (a.eval ρ) (i.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ssk_mem_m, Ssk_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l I, Formula.satisfies_mem_iff, ssk_wit_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem ssk_mem_decode_l (hE : Extensional M) {ω X u a i s x c R} (h : Smem_d I c X R) :
    Ssk_mem_d I ω X u a i s x ↔ M.mem x X ∧ Ssk_wit_d I ω c X u a i s x := by
  constructor
  · rintro ⟨d, S, hd, hx, ht⟩
    exact ⟨hx, (smem_unique_l I hE hd h).1 ▸ ht⟩
  · exact fun hx => ⟨c, R, h, hx⟩

/-- 参数依次为内部 ω、载体、基点、公式码、变量号和有限赋值图。 -/
def ssk_mem_s (𝒞 : OrderedPairConvention) : UnarySchema 6 := {
  body := ssk_mem_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

end YesMetaZFC.SetTheory.Internal
