module

public import VeilTest.GenTheoremsForms

public section

-- Public theorem declarations and their proof provenance survive .olean export/import.
run_cmd do
  for ns in #[`PublishedWPTheorems, `PublishedTRTheorems] do
    checkPublishedVCTheorems ns #[
      `initializer_doesNotThrow, `initializer_all_marked, `initializer_all_marked_tr,
      `keep_doesNotThrow, `keep_all_marked, `keep_all_marked_tr]
