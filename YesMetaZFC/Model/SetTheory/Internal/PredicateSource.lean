import YesMetaZFC.Model.SetTheory.Internal.EmbeddingSource
import YesMetaZFC.SetTheory.InnerModel.Separation.Formula

/-! # 从谓词结构嵌入读取原集合论公式

谓词图的对角线只记录 A。Foundation 保证 x∈y 恰好是 R(x,y)∧¬R(y,x)，
故先展开生产原子，再作统一关系替换，就能完整恢复原隶属语言。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem spred_mem_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R)
    {x y} (hx : M.mem x X) (hy : M.mem y X) :
    M.PairMember I x y R ∧ ¬ M.PairMember I y x R ↔ M.mem x y := by
  have asymm {x y} (hxy : M.mem x y) : ¬ M.mem y x := by
    intro hyx
    obtain ⟨P, hp⟩ := KP.exists_pair hKP x y
    obtain ⟨z, hz, hm⟩ := KP.mem_minimal_exists_d hKP ⟨x, (hp x).mpr (Or.inl rfl)⟩
    rcases (hp z).mp hz with rfl | rfl
    · exact hm y ((hp y).mpr (Or.inr rfl)) hyx
    · exact hm x ((hp x).mpr (Or.inl rfl)) hxy
  constructor
  · rintro ⟨hxy, hn⟩
    rcases ((h.2.2 x y).mp hxy).2.2 with hm | ⟨rfl, _⟩
    · exact hm
    · exact (hn hxy).elim
  · intro hxy
    refine ⟨(h.2.2 x y).mpr ⟨hx, hy, Or.inl hxy⟩, fun hyx => ?_⟩
    rcases ((h.2.2 y x).mp hyx).2.2 with hm | ⟨rfl, _⟩
    · exact asymm hxy hm
    · exact KP.mem_irrefl_d hKP _ hxy

def spred_core_l : {n : Nat} → Formula 0 n → Formula 1 n
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem s t => .conj (.mem s t) (.neg (.mem t s))
  | _, .atom _ h _ => by have h : (0 : Nat) < 0 := h; omega
  | _, .neg φ => .neg (spred_core_l φ)
  | _, .conj φ ψ => .conj (spred_core_l φ) (spred_core_l ψ)
  | _, .disj φ ψ => .disj (spred_core_l φ) (spred_core_l ψ)
  | _, .imp φ ψ => .imp (spred_core_l φ) (spred_core_l ψ)
  | _, .iff φ ψ => .iff (spred_core_l φ) (spred_core_l ψ)
  | _, .forallE φ => .forallE (spred_core_l φ)
  | _, .existsE φ => .existsE (spred_core_l φ)

theorem spred_core_closed_l {n} (φ : Formula 0 n) (hφ : φ.FreeClosed) : (spred_core_l φ).FreeClosed := by
  induction φ <;> simp only [spred_core_l, Definitional.Formula.FreeClosed] at hφ ⊢
  case atom _ h _ => have h : (0 : Nat) < 0 := h; omega
  case mem s t => exact ⟨hφ, hφ.2, hφ.1⟩
  case neg φ ih | forallE φ ih | existsE φ ih => exact ih hφ
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh => exact ⟨ih hφ.1, jh hφ.2⟩

theorem spred_core_sat_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} (φ : Formula 0 n)
    (ρ : Env (rt_model_l X hn) n) :
    Formula.satisfies (⟨ρ.bound, ρ.free⟩ : Env (smdl_structure_l I (R := R) h.1.2.1) n) (spred_core_l φ) ↔
      Definitional.Semantics.satisfies Semantics.interpretation ρ φ := by
  induction φ <;> simp only [spred_core_l, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Definitional.Semantics.satisfies]
  case atom _ ht _ => have ht : (0 : Nat) < 0 := ht; omega
  case mem s t => exact spred_mem_l I hKP h (s.eval ρ).property (t.eval ρ).property
  case neg φ ih => exact not_congr (ih ρ)
  case conj φ ψ ih jh => exact and_congr (ih ρ) (jh ρ)
  case disj φ ψ ih jh => exact or_congr (ih ρ) (jh ρ)
  case imp φ ψ ih jh => exact imp_congr (ih ρ) (jh ρ)
  case iff φ ψ ih jh => exact iff_congr (ih ρ) (jh ρ)
  case forallE φ ih => exact forall_congr' (fun x => ih (ρ.push x))
  case existsE φ ih => exact exists_congr (fun x => ih (ρ.push x))

/-- 带谓词初等嵌入对整个原隶属语言初等，不要求两个载体先满足 ZF。 -/
theorem spred_source_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hn : Nonempty {x : M.Domain // M.mem x X})
    (hm : Nonempty {x : M.Domain // M.mem x Y}) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (rt_model_l X hn) n) (η : Env (rt_model_l Y hm) n)
    (hp : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val j) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let ψ := spred_core_l (source_core_l φ)
  have tr (Z P Q c) (hz : Spred_d I c Z P Q) (hz' : Nonempty {x // M.mem x Z})
      (ρ : Env (rt_model_l Z hz') n) :=
    (spred_core_sat_l I (ZF.modelsKP hZF) hz hz' (source_core_l φ) ρ).trans (source_core_sat_l φ ρ)
  exact (tr X A R c hx hn ρ).symm.trans ((smap_source_l I hZF hω hx.1 hy.1 hj ψ
    (spred_core_closed_l _ (source_core_closed_l φ hφ)) ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ hp).trans
      (tr Y B S d hy hm η))

/-- 传递载体之间，原 Δ₀ 公式的保持可直接在背景模型中调用。 -/
theorem spred_delta_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    {n} (φ : Formula 1 n) (hf : φ.FreeClosed) (hd : φ.IsDelta0)
    (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  have hρ i := hj.1.1.input_mem_of_pairMember (hp i)
  have hη i := hj.1.1.output_mem_of_pairMember (hp i)
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨x, hxX⟩⟩
  let hm : Nonempty {x // M.mem x Y} := ⟨⟨y, hyY⟩⟩
  let ρ' : Env (rt_model_l X hn) n := ⟨fun i => ⟨ρ.bound i, hρ i⟩, fun _ => ⟨x, hxX⟩⟩
  let η' : Env (rt_model_l Y hm) n := ⟨fun i => ⟨η.bound i, hη i⟩, fun _ => ⟨y, hyY⟩⟩
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hx, hy, hj⟩ hn hm φ hf ρ' η' hp
  have hr : Formula.satisfies ρ' φ ↔ Formula.satisfies ρ φ :=
    (rt_model_delta_l hX hn hd ρ').trans (Formula.closed_env_l φ hf rfl)
  have hs : Formula.satisfies η' φ ↔ Formula.satisfies η φ :=
    (rt_model_delta_l hY hm hd η').trans (Formula.closed_env_l φ hf rfl)
  exact hr.symm.trans (tr.trans hs)

/-- 全称量词覆盖目标载体中的全部对象，包括不在 j 的像中的有限支撑。 -/
theorem spred_forall_delta_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    {n} (φ : Formula 1 (n + 1)) (hf : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) :
    (∀ x, M.mem x X → Formula.satisfies (ρ.push x) φ) ↔
      ∀ y, M.mem y Y → Formula.satisfies (η.push y) φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨x, hxX⟩⟩
  let hm : Nonempty {x // M.mem x Y} := ⟨⟨y, hyY⟩⟩
  let ρ' : Env (rt_model_l X hn) n :=
    ⟨fun i => ⟨ρ.bound i, hj.1.1.input_mem_of_pairMember (hp i)⟩, fun _ => ⟨x, hxX⟩⟩
  let η' : Env (rt_model_l Y hm) n :=
    ⟨fun i => ⟨η.bound i, hj.1.1.output_mem_of_pairMember (hp i)⟩, fun _ => ⟨y, hyY⟩⟩
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hx, hy, hj⟩ hn hm (.forallE φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hf) ρ' η' hp
  have hr (a : (rt_model_l X hn).Domain) : Formula.satisfies (ρ'.push a) φ ↔ Formula.satisfies (ρ.push a.val) φ :=
    (rt_model_delta_l hX hn hd _).trans (Formula.closed_env_l φ hf (by funext i; exact Fin.cases rfl (fun _ => rfl) i))
  have hs (b : (rt_model_l Y hm).Domain) : Formula.satisfies (η'.push b) φ ↔ Formula.satisfies (η.push b.val) φ :=
    (rt_model_delta_l hY hm hd _).trans (Formula.closed_env_l φ hf (by funext i; exact Fin.cases rfl (fun _ => rfl) i))
  simp only [Formula.satisfies_forall_iff] at tr
  exact ⟨fun h y hy => (hs ⟨y, hy⟩).mp (tr.mp (fun x => (hr x).mpr (h x.val x.property)) ⟨y, hy⟩),
    fun h x hx => (hr ⟨x, hx⟩).mp (tr.mpr (fun y => (hs y).mpr (h y.val y.property)) ⟨x, hx⟩)⟩

theorem spred_predicate_l (hZF : M.Models ZF) {ω X A Y B j x y} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hp : M.PairMember I x y j) : M.mem x A ↔ M.mem y B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let x' : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨x, hj.1.1.input_mem_of_pairMember hp⟩
  let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, hj.1.1.output_mem_of_pairMember hp⟩
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj (n := 1) (.mem (.bound 0) (.bound 0))
    (by simp [Definitional.Formula.FreeClosed]) ⟨fun _ => x', fun _ => x'⟩ ⟨fun _ => y', fun _ => y'⟩ (fun _ => hp)
  simp only [Formula.satisfies_mem_iff] at tr
  exact (spred_read_l I (ZF.modelsKP hZF) hx x x).1.symm.trans (tr.trans
    (spred_read_l I (ZF.modelsKP hZF) hy y y).1)

/-- 谓词自身的传递性由扩张语言的初等性保持，不能只用遗忘谓词后的嵌入代替。 -/
theorem spred_transitive_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hY : M.TransitiveSet Y) (hA : M.TransitiveSet A) : M.TransitiveSet B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let φ : Formula 1 0 := .forallE (.forallE (.imp
    (.conj (.mem .newest .newest) (.conj (.mem (.bound 1) .newest) (.neg (.mem .newest (.bound 1)))))
    (.mem (.bound 1) (.bound 1))))
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by simp [φ, Definitional.Formula.FreeClosed])
    ⟨Fin.elim0, fun _ => ⟨x, hxX⟩⟩ ⟨Fin.elim0, fun _ => ⟨y, hyY⟩⟩ (fun i => Fin.elim0 i)
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff] at tr
  have hs := tr.mp (fun a b hb => (spred_read_l I (ZF.modelsKP hZF) hx a.val a.val).1.mpr
    (hA b.val ((spred_read_l I (ZF.modelsKP hZF) hx b.val b.val).1.mp hb.1) a.val
      ((spred_mem_l I (ZF.modelsKP hZF) hx a.property b.property).mp hb.2)))
  intro b hb a hab
  let b' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨b, hy.2.1 b hb⟩
  let a' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨a, hY b b'.property a hab⟩
  exact (spred_read_l I (ZF.modelsKP hZF) hy a a).1.mp (hs a' b'
    ⟨(spred_read_l I (ZF.modelsKP hZF) hy b b).1.mpr hb,
      (spred_mem_l I (ZF.modelsKP hZF) hy a'.property b'.property).mpr hab⟩)

section
variable (hZF : M.Models ZF) {ω X A Y B j : M.Domain} (hω : M.IsOmega ω)
  (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
include hZF hω h hX hY

theorem spred_entry_l {a a' b b' F F'} (ha : M.PairMember I a a' j)
    (hb : M.PairMember I b b' j) (hF : M.PairMember I F F' j) : Rd_entry_d a b F ↔ Rd_entry_d a' b' F' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 3) (rd_entry0_m (.bound 2) (.bound 1) (.bound 0))
    (rd_entry0_m_freeClosed _ _ _ rfl rfl rfl) (rd_entry0_delta_l ..)
    ⟨Fin.cases F (Fin.cases b (fun _ => a)), fun _ => a⟩
    ⟨Fin.cases F' (Fin.cases b' (fun _ => a')), fun _ => a'⟩
    (Fin.cases hF (Fin.cases hb (fun _ => ha)))
  simp only [rd_entry0_sat_l hZF.1] at tr
  exact tr

theorem spred_function_l {D D' U U' F F'} (hD : M.PairMember I D D' j)
    (hU : M.PairMember I U U' j) (hF : M.PairMember I F F' j) : Fn0_d D U F ↔ Fn0_d D' U' F' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 3) (fn0_m (.bound 2) (.bound 1) (.bound 0))
    (fn0_m_freeClosed _ _ _ rfl rfl rfl) (fn0_delta_l ..)
    ⟨Fin.cases F (Fin.cases U (fun _ => D)), fun _ => D⟩
    ⟨Fin.cases F' (Fin.cases U' (fun _ => D')), fun _ => D'⟩
    (Fin.cases hF (Fin.cases hU (fun _ => hD)))
  simp only [fn0_sat_l hZF.1] at tr
  exact tr

end

end YesMetaZFC.SetTheory.Internal
