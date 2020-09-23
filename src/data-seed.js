import { Article } from "./data-source";

import articleCharacterTables from "./article-character-tables.txt";

export function getSeed() {
  return {
    articles: [
      new Article({
        id: "character-tables",
        title:
          "Techniques for constructing character tables",
        text: articleCharacterTables,
      }),
    ],

    references: [],
  };
}
