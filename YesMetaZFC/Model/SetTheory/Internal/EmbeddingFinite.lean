import YesMetaZFC.Model.SetTheory.Internal.SourceFinite

/-! # 初等映射固定内部自然数并搬运有限函数

归纳使用实际图条目原公式，因而覆盖全部内部自然数。有限坐标保持据此
适用于非标准长度，不以宿主的有限列表代替对象模型中的序列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.natural_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) : ∀ n, M.mem n ω → M.PairMember I n n q := by
  let φ : UnarySchema 1 := { body := rd_entry_m .newest .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  have read n : φ.denote ρ n ↔ M.PairMember I n n q := rd_entry_sat_l hZF.1 ..
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      obtain ⟨z₀, hz₀, hzω⟩ := hω.1.1
      have eq := hZF.1.eq_of_same_members z₀ z (fun x => iff_of_false (hz₀ x) (hz x))
      subst z₀
      obtain ⟨z', _, hzz⟩ := hq.1.1.2.2 z (hX ω hωX z hzω)
      have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 1)
        (Formula.forallMem .newest .falsum) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])
        (.forallMem _ .falsum) ⟨fun _ => z, fun _ => z⟩ ⟨fun _ => z', fun _ => z'⟩ (fun _ => hzz)
      simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff] at tr
      have ez := hZF.1.eq_of_same_members z' z (fun x => iff_of_false (tr.mp hz x) (hz x))
      exact (read z).mpr (ez ▸ hzz)
    · intro n hnω ih m hs
      obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hnω
      have eq := Structure.SuccessorOf.eq hZF.1 hm₀ hs
      subst m₀
      obtain ⟨m', _, hmm⟩ := hq.1.1.2.2 m (hX ω hωX m hmω)
      have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 2)
        (KP.succ0_m .newest (.bound 1)) (by simp -implicitDefEqProofs)
        (KP.succ0_delta_l ..) ⟨Fin.cases m (fun _ => n), fun _ => n⟩
        ⟨Fin.cases m' (fun _ => n), fun _ => n⟩ (Fin.cases hmm (fun _ => (read n).mp ih))
      simp only [KP.succ0_sat_l hZF.1] at tr
      exact (read m).mpr (Structure.SuccessorOf.eq hZF.1 (tr.mp hs) hs ▸ hmm)
  exact fun n hn => (read n).mp (all n hn)

theorem Smap_d.function_l {ω c d X R Y S q A A' B B' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : M.PairMember I A A' q) (hB : M.PairMember I B B' q) (hf : M.PairMember I f f' q) :
    Fn0_d A B f ↔ Fn0_d A' B' f' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 3) (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    ⟨Fin.cases f (Fin.cases B (fun _ => A)), fun _ => A⟩
    ⟨Fin.cases f' (Fin.cases B' (fun _ => A')), fun _ => A'⟩ (Fin.cases hf (Fin.cases hB (fun _ => hA)))
  simp only [fn0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.entry_l {ω c d X R Y S q a a' b b' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (ha : M.PairMember I a a' q) (hb : M.PairMember I b b' q) (hf : M.PairMember I f f' q) :
    Rd_entry_d a b f ↔ Rd_entry_d a' b' f' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 3) (rd_entry0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    ⟨Fin.cases f (Fin.cases b (fun _ => a)), fun _ => a⟩
    ⟨Fin.cases f' (Fin.cases b' (fun _ => a')), fun _ => a'⟩ (Fin.cases hf (Fin.cases hb (fun _ => ha)))
  simp only [rd_entry0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.forall_delta_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    {n} (φ : Formula 1 (n + 1)) (hc : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) q) :
    (∀ x, M.mem x X → Formula.satisfies (ρ.push x) φ) ↔ ∀ y, M.mem y Y → Formula.satisfies (η.push y) φ := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact spred_forall_delta_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ hX hY φ hc hd ρ η hp

theorem Smap_d.subset_l {ω c d X R Y S q A A' B B' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : M.PairMember I A A' q) (hB : M.PairMember I B B' q) :
    M.MemberSubset A B ↔ M.MemberSubset A' B' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 2) (Formula.subset (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (.atom _ _ _) ⟨Fin.cases B (fun _ => A), fun _ => A⟩
    ⟨Fin.cases B' (fun _ => A'), fun _ => A'⟩ (Fin.cases hB (fun _ => hA))
  simp only [Formula.satisfies_subset_iff] at tr
  exact tr

theorem Smap_d.composition_l {ω c d X R Y S q A A' B B' C C' t t' f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : Rd_entry_d A A' q) (hB : Rd_entry_d B B' q) (hC : Rd_entry_d C C' q)
    (ht : Rd_entry_d t t' q) (hf : Rd_entry_d f f' q) (hg : Rd_entry_d g g' q) :
    Cp0_d A B C t f g ↔ Cp0_d A' B' C' t' f' g' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 6)
    (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (cp0_delta_l ..)
    ⟨Fin.cases g (Fin.cases f (Fin.cases t (Fin.cases C (Fin.cases B (fun _ => A))))), fun _ => A⟩
    ⟨Fin.cases g' (Fin.cases f' (Fin.cases t' (Fin.cases C' (Fin.cases B' (fun _ => A'))))), fun _ => A'⟩
    (Fin.cases hg (Fin.cases hf (Fin.cases ht (Fin.cases hC (Fin.cases hB (fun _ => hA))))))
  simp only [cp0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.finite_fixed_l {ω c d X R Y S q n f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (hnω : M.mem n ω) (hfX : M.mem f X) (hf : Fn0_d n ω f) : M.PairMember I f f q := by
  obtain ⟨f', _, hff⟩ := hq.1.1.2.2 f hfX
  have natural := hq.natural_l hZF hω hX hY hm hn hωX
  have hf' := (hq.function_l hZF hω hX hY hm hn (natural n hnω) (hq.omega_l I hZF hω hX hY hm hn hωX) hff).mp hf
  have eq := hf'.ext_l hZF.1 hf (fun i hi => by
    obtain ⟨x, hx, hix⟩ := hf.2.1 i hi
    exact ⟨x, (hq.entry_l hZF hω hX hY hm hn (natural i (hω.transitive hZF n hnω i hi)) (natural x hx) hff).mp hix, hix⟩)
  exact eq ▸ hff

theorem Smap_d.finite_injection_l {ω c d X R Y S q n A A' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (hnω : M.mem n ω) (hA : M.PairMember I A A' q) (hff : M.PairMember I f f' q)
    (hf : M.IsSetInjectionFromTo I f n A) : M.IsSetInjectionFromTo I f' n A' := by
  have natural := hq.natural_l hZF hω hX hY hm hn hωX
  have hf' := fn0_function_l (ZF.modelsKP hZF) ((hq.function_l hZF hω hX hY hm hn (natural n hnω) hA hff).mp
    (fn0_of_function_l (ZF.modelsKP hZF) hf.1))
  have back i y (hiy : Rd_entry_d i y f') : ∃ x, Rd_entry_d i x f ∧ M.PairMember I x y q := by
    have hi := hf'.input_mem_of_pairMember hiy
    obtain ⟨x, hx, hix⟩ := hf.1.2.2 i hi
    obtain ⟨x', _, hxx⟩ := hq.1.1.2.2 x (hX A (hq.1.1.input_mem_of_pairMember hA) x hx)
    have hix' := (hq.entry_l hZF hω hX hY hm hn (natural i (hω.transitive hZF n hnω i hi)) hxx hff).mp hix
    exact ⟨x, hix, hf'.1.2 i x' y hix' hiy ▸ hxx⟩
  refine ⟨hf', fun i j y hi hj => ?_⟩
  obtain ⟨x, hix, hxy⟩ := back i y hi
  obtain ⟨z, hjz, hzy⟩ := back j y hj
  exact hf.2 i j z (hq.1.2 x z y hxy hzy ▸ hix) hjz

end YesMetaZFC.SetTheory.Internal
