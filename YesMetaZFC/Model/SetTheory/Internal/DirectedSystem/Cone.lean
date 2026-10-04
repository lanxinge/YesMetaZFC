import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.WellFounded

/-! # 由实际相容嵌入族构造定向系统

一张标签图与一张共同目标中的取值图编码整个族。分量内取值单射、像随指标
增大而包含时，过渡图由相同取值唯一确定；无需另给恒等、复合或关系保持证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_cone_system_l (hZF : M.Models ZF) {J L A p Y V e : M.Domain}
    (ho : Di_order_d J L) (hp : Fn0_d A J p) (he : Fn0_d A Y e)
    (hinj : ∀ a b i x, Rd_entry_d a i p → Rd_entry_d b i p → Rd_entry_d a x e → Rd_entry_d b x e → a = b)
    (hmono : ∀ a i j x, Rd_entry_d a i p → Rd_entry_d i j L → Rd_entry_d a x e →
      ∃ b, Rd_entry_d b j p ∧ Rd_entry_d b x e) : ∃ T R,
      Di_system_d J L A p T R ∧
      (∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
        (Rd_entry_d a b T ↔ Rd_entry_d i j L ∧ x = y)) ∧
      ∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
        (Rd_entry_d a b R ↔ i = j ∧ Rd_entry_d x y V) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push e).push L
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (rd_entry_m (.bound 4) (.bound 2) (.bound 7)) (.conj
      (rd_entry_m (.bound 3) (.bound 1) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) .newest (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 2) (.bound 1) (.bound 5)))))))) }
  have sat a b : φ.denote ρ a b ↔ ∃ i j x, Rd_entry_d a i p ∧ Rd_entry_d b j p ∧
      Rd_entry_d a x e ∧ Rd_entry_d b x e ∧ Rd_entry_d i j L := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨T, _, ht⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have fp := fn0_function_l (ZF.modelsKP hZF) hp
  have fe := fn0_function_l (ZF.modelsKP hZF) he
  have ts a b i j x y (hai : Rd_entry_d a i p) (hbj : Rd_entry_d b j p)
      (hax : Rd_entry_d a x e) (hby : Rd_entry_d b y e) : Rd_entry_d a b T ↔ Rd_entry_d i j L ∧ x = y := by
    change M.PairMember I a b T ↔ _
    rw [ht a b, sat a b]
    constructor
    · rintro ⟨_, _, i', j', z, hai', hbj', haz, hbz, hij⟩
      exact ⟨fp.1.2 a i' i hai' hai ▸ fp.1.2 b j' j hbj' hbj ▸ hij,
        (fe.1.2 a z x haz hax).symm.trans (fe.1.2 b z y hbz hby)⟩
    · rintro ⟨hij, eq⟩
      exact ⟨(hp.bound_l hai).1, (hp.bound_l hbj).1, i, j, x, hai, hbj, hax, eq.symm ▸ hby, hij⟩
  let η := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push e).push V
  let ψ : BinarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (rd_entry_m (.bound 4) (.bound 2) (.bound 7)) (.conj
      (rd_entry_m (.bound 3) (.bound 2) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) (.bound 1) (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 1) .newest (.bound 5)))))))) }
  have sat' a b : ψ.denote η a b ↔ ∃ i x y, Rd_entry_d a i p ∧ Rd_entry_d b i p ∧
      Rd_entry_d a x e ∧ Rd_entry_d b y e ∧ Rd_entry_d x y V := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η A
  have rs a b i j x y (hai : Rd_entry_d a i p) (hbj : Rd_entry_d b j p)
      (hax : Rd_entry_d a x e) (hby : Rd_entry_d b y e) : Rd_entry_d a b R ↔ i = j ∧ Rd_entry_d x y V := by
    change M.PairMember I a b R ↔ _
    rw [hr a b, sat' a b]
    constructor
    · rintro ⟨_, _, k, u, v, hak, hbk, hau, hbv, huv⟩
      exact ⟨(fp.1.2 a k i hak hai).symm.trans (fp.1.2 b k j hbk hbj),
        fe.1.2 a u x hau hax ▸ fe.1.2 b v y hbv hby ▸ huv⟩
    · rintro ⟨eq, hxy⟩
      exact ⟨(hp.bound_l hai).1, (hp.bound_l hbj).1, i, x, y, hai, eq.symm ▸ hbj, hax, hby, hxy⟩
  have tb a b (hab : Rd_entry_d a b T) : M.mem a A ∧ M.mem b A :=
    ⟨((ht a b).mp hab).1, ((ht a b).mp hab).2.1⟩
  refine ⟨T, R, ⟨ho, hp, tb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ts, rs⟩
  · intro a b i j hai hbj hab
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (hp.bound_l hbj).1
    exact ((ts a b i j x y hai hbj hax hby).mp hab).1
  · intro a ha
    obtain ⟨i, hi, hai⟩ := hp.2.1 a ha
    obtain ⟨x, _, hax⟩ := he.2.1 a ha
    exact (ts a a i i x x hai hai hax hax).mpr ⟨ho.refl i hi, rfl⟩
  · intro a b c hab hbc
    obtain ⟨i, _, hai⟩ := hp.2.1 a (tb a b hab).1
    obtain ⟨j, _, hbj⟩ := hp.2.1 b (tb a b hab).2
    obtain ⟨k, _, hck⟩ := hp.2.1 c (tb b c hbc).2
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a b hab).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb a b hab).2
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb b c hbc).2
    obtain ⟨hij, exy⟩ := (ts a b i j x y hai hbj hax hby).mp hab
    obtain ⟨hjk, eyz⟩ := (ts b c j k y z hbj hck hby hcz).mp hbc
    exact (ts a c i k x z hai hck hax hcz).mpr ⟨ho.trans i j k hij hjk, exy.trans eyz⟩
  · intro a i j hai hij
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨b, hbj, hbx⟩ := hmono a i j x hai hij hax
    exact ⟨b, hbj, (ts a b i j x x hai hbj hax hbx).mpr ⟨hij, rfl⟩⟩
  · intro a b c j hbj hcj hab hac
    obtain ⟨i, _, hai⟩ := hp.2.1 a (tb a b hab).1
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a b hab).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb a b hab).2
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb a c hac).2
    have ey := ((ts a b i j x y hai hbj hax hby).mp hab).2
    have ez := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    exact hinj b c j x hbj hcj (ey.symm ▸ hby) (ez.symm ▸ hcz)
  · intro a b c i hai hbi hac hbc
    obtain ⟨j, _, hcj⟩ := hp.2.1 c (tb a c hac).2
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a c hac).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb b c hbc).1
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb a c hac).2
    have ex := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    have ey := ((ts b c i j y z hbi hcj hby hcz).mp hbc).2
    exact hinj a b i z hai hbi (ex ▸ hax) (ey ▸ hby)
  · intro a b hab
    obtain ⟨i, _, _, hai, hbi, _⟩ := (sat' a b).mp ((hr a b).mp hab).2.2
    exact ⟨i, hai, hbi⟩
  · intro a b i c d j hai hbi hcj hdj hac hbd
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (hp.bound_l hbi).1
    obtain ⟨z, _, hcz⟩ := he.2.1 c (hp.bound_l hcj).1
    obtain ⟨w, _, hdw⟩ := he.2.1 d (hp.bound_l hdj).1
    have ex := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    have ey := ((ts b d i j y w hbi hdj hby hdw).mp hbd).2
    have h₁ : Rd_entry_d a b R ↔ Rd_entry_d x y V :=
      (rs a b i i x y hai hbi hax hby).trans ⟨And.right, fun hr => ⟨rfl, hr⟩⟩
    have h₂ : Rd_entry_d c d R ↔ Rd_entry_d z w V :=
      (rs c d j j z w hcj hdj hcz hdw).trans ⟨And.right, fun hr => ⟨rfl, hr⟩⟩
    exact h₁.trans (by rw [ex, ey]; exact h₂.symm)

end YesMetaZFC.SetTheory.Internal
