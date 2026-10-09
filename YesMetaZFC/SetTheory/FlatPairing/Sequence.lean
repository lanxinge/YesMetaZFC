import YesMetaZFC.SetTheory.FlatPairing.Rank
import YesMetaZFC.SetTheory.Descriptive.MapIteration

/-! # 全部内部有限元组的平坦编码

将赋值的前 n 项反复配对。递归指标是模型自己的 ω；轨道图只需是 Vν 的
子集，每个有限前缀的编码则已经属于 Vν。这里不把内部自然数换成外部 Nat。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fs_trace_d (ω X f H : M.Domain) : Prop := M.IsSetFunctionFromTo I H ω X ∧
  (∀ z, (∀ x, ¬ M.mem x z) → M.PairMember I z z H) ∧
  ∀ i j p q x, M.SuccessorOf j i → M.PairMember I i p H → M.PairMember I j q H →
    M.PairMember I i x f → I.Codes q p x

def fs_trace_m {d} (ω X f H : Term d) : Formula 1 d := .conj
  (Formula.isFunctionFromTo 𝒞 H ω X) (.conj
    (.forallE (.imp (Formula.isEmpty .newest) (Formula.orderedPairMem 𝒞 .newest .newest H.weaken)))
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (Formula.isSuccessor (.bound 3) (.bound 4))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 2) H.weaken.weaken.weaken.weaken.weaken)
        (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken.weaken)
          (.imp (Formula.orderedPairMem 𝒞 (.bound 4) .newest f.weaken.weaken.weaken.weaken.weaken)
            (𝒞.code (.bound 1) (.bound 2) .newest)))))))))))
derive_free_closed fs_trace_m

theorem fs_trace_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X f H : Term d) :
    Formula.satisfies ρ (fs_trace_m (𝒞 := 𝒞) ω X f H) ↔
      Fs_trace_d I (ω.eval ρ) (X.eval ρ) (f.eval ρ) (H.eval ρ) := by
  simp only [fs_trace_m, Fs_trace_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff, I.satisfies_code_iff,
    Definitional.Term.eval_weaken]; rfl

private def fs_next_m {d} (f a b : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (𝒞.code a.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3)) (.conj
    (Formula.isSuccessor (.bound 2) (.bound 4)) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 4) .newest f.weaken.weaken.weaken.weaken.weaken) (.conj
    (𝒞.code (.bound 1) (.bound 3) .newest)
    (𝒞.code b.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))))))))))
derive_free_closed fs_next_m

private theorem fs_next_sat_l {d} (ρ : Env M d) (f a b : Term d) :
    Formula.satisfies ρ (fs_next_m (𝒞 := 𝒞) f a b) ↔ ∃ i p j q x,
      I.Codes (a.eval ρ) i p ∧ M.SuccessorOf j i ∧ M.PairMember I i x (f.eval ρ) ∧
        I.Codes q p x ∧ I.Codes (b.eval ρ) j q := by
  simp only [fs_next_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

/-- 对配对闭合的集合，实际构造所有内部有限前缀的编码轨道。 -/
theorem fs_trace_exists_l (hZF : M.Models ZF) {ω X f : M.Domain} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hz : ∀ z, (∀ x, ¬ M.mem x z) → M.mem z X)
    (closed : ∀ p x q, M.mem p X → M.mem x X → I.Codes q p x → M.mem q X) :
    ∃ H, Fs_trace_d I ω X f H := by
  obtain ⟨S, hS⟩ := ZF.exists_cartesianProduct hZF I ω X
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  let φ : BinarySchema 1 := { body := fs_next_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  have read a b := fs_next_sat_l I ((ρ.push a).push b) (.bound 2) (.bound 1) .newest
  obtain ⟨F, hF, val⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := S) (target := S) (by
    intro a ha
    obtain ⟨i, hi, p, hp, code⟩ := (hS a).mp ha
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨j, succ, _⟩ := hω.1.2 i hi
    obtain ⟨q, cq⟩ := I.total p x
    obtain ⟨b, cb⟩ := I.total j q
    exact ⟨b, (read a b).mpr ⟨i, p, j, q, x, code, succ, hix, cq, cb⟩⟩) (by
    intro a _ b c hb hc
    obtain ⟨i, p, j, q, x, ca, sj, fx, cq, cb⟩ := (read a b).mp hb
    obtain ⟨i', p', j', q', x', ca', sj', fx', cq', cc⟩ := (read a c).mp hc
    obtain ⟨ei, ep⟩ := I.injective ca' ca
    subst i'; subst p'
    have ej := Structure.SuccessorOf.eq hZF.1 sj' sj
    have ex := hf.1.2 i x' x fx' fx
    subst j'; subst x'
    have eq := I.unique cq' cq
    subst q'
    exact I.unique cb cc) (by
    intro a b ha hb
    obtain ⟨i, hi, p, hp, ca⟩ := (hS a).mp ha
    obtain ⟨i', p', j, q, x, ca', sj, fx, cq, cb⟩ := (read a b).mp hb
    obtain ⟨ei, ep⟩ := I.injective ca' ca
    subst i'; subst p'
    obtain ⟨j', sj', hj'⟩ := hω.1.2 i hi
    exact (hS b).mpr ⟨j, Structure.SuccessorOf.eq hZF.1 sj' sj ▸ hj', q,
      closed p x q hp (hf.output_mem_of_pairMember fx) cq, cb⟩)
  obtain ⟨z, ez, hzω⟩ := hω.1.1
  obtain ⟨a, ca⟩ := I.total z z
  obtain ⟨G, hG, zero, step⟩ := ZFC.iterate_l I hZF hω hF ((hS a).mpr ⟨z, hzω, z, hz z ez, ca⟩)
  have next {i j s t} (succ : M.SuccessorOf j i) (hs : M.PairMember I i s G) (ht : M.PairMember I j t G) :=
    (read s t).mp ((val s t).mp (step i j s t succ hs ht)).2
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : UnarySchema 1 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (.existsE (𝒞.code (.bound 1) (.bound 2) .newest))) }
  have index k : ψ.denote η k ↔ ∀ s, M.PairMember I k s G → ∃ p, I.Codes s k p := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff, I.satisfies_code_iff]; rfl
  have aligned : ∀ k, M.mem k ω → ∀ s, M.PairMember I k s G → ∃ p, I.Codes s k p := by
    apply hω.induction
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ η ω
      exact ⟨C, fun k => (hC k).trans (and_congr_right fun _ => index k)⟩
    · intro e he s hs
      have eq := hZF.1.eq_of_same_members z e (fun x => iff_of_false (ez x) (he x))
      have es := hG.1.2 e s a hs (zero e he)
      exact ⟨z, eq ▸ es.symm ▸ ca⟩
    · intro i hi ih j succ t ht
      obtain ⟨s, _, hs⟩ := hG.2.2 i hi
      obtain ⟨p, cs⟩ := ih s hs
      obtain ⟨i', p', j', q, x, cs', sj, _, _, ct⟩ := next succ hs ht
      obtain ⟨ei, ep⟩ := I.injective cs' cs
      subst i'; subst p'
      exact ⟨q, Structure.SuccessorOf.eq hZF.1 sj succ ▸ ct⟩
  let χ : BinarySchema 1 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (𝒞.code .newest (.bound 2) (.bound 1))) }
  have project k p : χ.denote η k p ↔ ∃ s, M.PairMember I k s G ∧ I.Codes s k p := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]; rfl
  obtain ⟨H, hH, ph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ η (source := ω) (target := X) (by
    intro k hk
    obtain ⟨s, _, hs⟩ := hG.2.2 k hk
    obtain ⟨p, cp⟩ := aligned k hk s hs
    exact ⟨p, (project k p).mpr ⟨s, hs, cp⟩⟩) (by
    intro k _ p q hp hq
    obtain ⟨s, hs, cs⟩ := (project k p).mp hp
    obtain ⟨t, ht, ct⟩ := (project k q).mp hq
    have eq := hG.1.2 k t s ht hs
    exact (I.injective cs (eq ▸ ct)).2) (by
    intro k p _ hp
    obtain ⟨s, hs, cs⟩ := (project k p).mp hp
    obtain ⟨i, _, q, hq, cq⟩ := (hS s).mp (hG.output_mem_of_pairMember hs)
    exact (I.injective cq cs).2 ▸ hq)
  refine ⟨H, hH, ?_, ?_⟩
  · intro e he
    have eq := hZF.1.eq_of_same_members z e (fun x => iff_of_false (ez x) (he x))
    exact (ph e e).mpr ⟨eq ▸ hzω, (project e e).mpr ⟨a, zero e he, eq ▸ ca⟩⟩
  · intro i j p q x succ hp hq hx
    obtain ⟨s, hs, cs⟩ := (project i p).mp ((ph i p).mp hp).2
    obtain ⟨t, ht, ct⟩ := (project j q).mp ((ph j q).mp hq).2
    obtain ⟨i', p', j', q', x', cs', _, hx', cq, ct'⟩ := next succ hs ht
    obtain ⟨ei, ep⟩ := I.injective cs' cs
    subst i'; subst p'
    obtain ⟨ej, eq⟩ := I.injective ct' ct
    subst j'; subst q'
    exact hf.1.2 i x' x hx' hx ▸ cq

end YesMetaZFC.SetTheory
